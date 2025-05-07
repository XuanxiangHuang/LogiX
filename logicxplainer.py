#!/usr/bin/env python
# -*- coding:utf-8 -*-
#
#   logic-based explainer
#   Author: Xuanxiang Huang
#
################################################################################
from abc import ABC, abstractmethod
import time
from pysat.formula import IDPool
from pysat.solvers import Solver as SAT_Solver
################################################################################


class LogicXplainer(ABC):
    def __init__(self, custom_object, verbose=1):
        """
        :param custom_object: some data structure that contains all the information needed
        :param verbose:
        """
        self.custom_object = custom_object
        self.verbose = verbose

    @abstractmethod
    def waxp(self, fixed, *additional_info):
        """
            User-defined procedure waxp.
            Should test the custom_object with a list of fixed features and some additional information,
            and return the result.
        """
        pass

    @abstractmethod
    def wcxp(self, universal, *additional_info):
        """
            User-defined procedure waxp.
            Should test the custom_object with a list of universal features and some additional information,
            and return the result.
        """
        pass

    def axp_del(self, fixed, *additional_info):
        """
            Compute one abductive explanation (AXp) using deletion based algorithm.

            :param fixed: a list of features declared as fixed.
            :param additional_info: additional information.
            :return: one abductive explanation,
                        each element in the return AXp is a feature index.
        """

        time_start = time.perf_counter()

        fix = fixed[:]
        for i in fix:
            tmp_fix = fix[:]
            tmp_fix.remove(i)
            if self.waxp(tmp_fix, *additional_info):
                fix = tmp_fix
        axp = fix

        time_end = time.perf_counter()

        if self.verbose:
            if self.verbose == 1:
                print(f"AXp (Del): {axp}")
            print("Runtime: {0:.3f}".format(time_end - time_start))

        return axp

    def axp_qxp(self, fixed, *additional_info):
        """
            Compute one abductive explanation (AXp) using divide-and-conquer.
            (QuickExplain algorithm)
            :param fixed: a list of features declared as fixed.
            :param additional_info: additional information.
            :return: one abductive explanation,
                        each element in the return AXp is a feature index.
        """

        def qxp_recur(B, Z, newB=False):
            if newB and self.waxp(B, *additional_info):
                return []
            if len(Z) == 1:
                return Z
            u = int(len(Z) / 2)
            Z1 = Z[:u]
            Z2 = Z[u:]
            Q2 = qxp_recur(B + Z1, Z2, len(Z1) > 0)
            Q1 = qxp_recur(B + Q2, Z1, len(Q2) > 0)
            return Q1 + Q2

        time_start = time.perf_counter()

        axp = qxp_recur([], fixed, False)

        time_end = time.perf_counter()

        if self.verbose:
            if self.verbose == 1:
                print(f"AXp (Qxp): {axp}")
            print("Runtime: {0:.3f}".format(time_end - time_start))

        return axp

    def cxp_del(self, universal, *additional_info):
        """
            Compute one contrastive explanation (CXp) using deletion based algorithm.

            :param universal: a list of features declared as universal.
            :param additional_info: additional information.
            :return: one contrastive explanation,
                        each element in the return CXp is a feature index.
        """

        time_start = time.perf_counter()

        univ = universal[:]
        for i in univ:
            tmp_univ = univ[:]
            tmp_univ.remove(i)
            if self.wcxp(tmp_univ, *additional_info):
                univ = tmp_univ
        cxp = univ

        time_end = time.perf_counter()

        if self.verbose:
            if self.verbose == 1:
                print(f"CXp (Del): {cxp}")
            print("Runtime: {0:.3f}".format(time_end - time_start))

        return cxp

    def cxp_qxp(self, universal, *additional_info):
        """
            Compute one contrastive explanation (CXp) using divide-and-conquer.
            (QuickExplain algorithm)
            :param universal: a list of features declared as universal.
            :param additional_info: additional information.
            :return: one contrastive explanation,
                        each element in the return CXp is a feature index.
        """

        def qxp_recur(B, Z, newB=False):
            if newB and self.wcxp(B, *additional_info):
                return []
            if len(Z) == 1:
                return Z
            u = int(len(Z) / 2)
            Z1 = Z[:u]
            Z2 = Z[u:]
            Q2 = qxp_recur(B + Z1, Z2, len(Z1) > 0)
            Q1 = qxp_recur(B + Q2, Z1, len(Q2) > 0)
            return Q1 + Q2

        time_start = time.perf_counter()

        cxp = qxp_recur([], universal, False)

        time_end = time.perf_counter()

        if self.verbose:
            if self.verbose == 1:
                print(f"CXp (Qxp): {cxp}")
            print("Runtime: {0:.3f}".format(time_end - time_start))

        return cxp

    def enum(self, feats_idx, alg='del', *additional_info):
        """
            Enumerate all (abductive and contrastive) explanations, using MARCO algorithm.
            :param feats_idx: set of feature indices
            :param alg: algorithm used to compute one explanation, 'del' or 'qxp'
            :param additional_info: additional information.
            :return: a list of all AXps, a list of all CXps.
        """

        #########################################
        vpool = IDPool()

        def new_var(name):
            """
                Inner function,
                Find or new a PySAT variable.
                See PySat.

                :param name: name of variable
                :return: index of variable
            """
            return vpool.id(f'{name}')

        #########################################

        time_start = time.perf_counter()

        axps = []
        cxps = []

        for i in feats_idx:
            new_var(f'u_{i}')

        with SAT_Solver(name="glucose4") as slv:
            while slv.solve():
                # first model is empty
                model = slv.get_model()
                univ = []
                for lit in model:
                    name = vpool.obj(abs(lit)).split(sep='_')
                    univ.extend([int(name[1])] if lit > 0 else [])  # lit > 0 means universal
                fix = [i for i in feats_idx if i not in univ]
                if self.wcxp(univ, *additional_info):
                    if alg == 'del':
                        cxp = self.cxp_del(univ, *additional_info)
                    elif alg == 'qxp':
                        cxp = self.cxp_qxp(univ, *additional_info)
                    # fix one feature next time
                    slv.add_clause([-new_var(f'u_{i}') for i in cxp])
                    cxps.append(cxp)
                else:
                    if alg == 'del':
                        axp = self.axp_del(fix, *additional_info)
                    elif alg == 'qxp':
                        axp = self.axp_qxp(fix, *additional_info)
                    # free one feature next time
                    slv.add_clause([new_var(f'u_{i}') for i in axp])
                    axps.append(axp)

        time_end = time.perf_counter()
        if self.verbose:
            print('#AXp:', len(axps))
            print('#CXp:', len(cxps))
            print("Runtime: {0:.3f}".format(time_end - time_start))

        return axps, cxps

    def check_axp(self, axp, *additional_info):
        """
            Check if given axp is 1) a weak AXp and 2) subset-minimal.

            :param axp: given axp.
            :return: true if given axp is an AXp
                        else false.
        """

        fix = axp[:]
        # 1) a weak AXp ?
        if not self.waxp(fix, *additional_info):
            print(f'{axp} is not a weak AXp')
            return False
        # 2) subset-minimal ?
        for i in fix:
            tmp_fix = fix[:]
            tmp_fix.remove(i)
            if self.waxp(tmp_fix, *additional_info):
                print(f'{axp} is not subset-minimal')
                return False
        return True

    def check_cxp(self, cxp, *additional_info):
        """
            Check if given cxp is 1) a weak CXp and 2) subset-minimal.

            :param cxp: given cxp.
            :return: true if given cxp is an CXp
                        else false.
        """

        univ = cxp[:]
        # 1) a weak CXp ?
        if not self.wcxp(univ, *additional_info):
            print(f'{cxp} is not a weak CXp')
            return False
        # 2) subset-minimal ?
        for i in univ:
            tmp_univ = univ[:]
            tmp_univ.remove(i)
            if self.wcxp(tmp_univ, *additional_info):
                print(f'{cxp} is not subset-minimal')
                return False
        return True
