"""
Provides an interface to modelling networks with a SMT Solver
Author: Ameya Daigavane
"""
from abc import ABC, abstractmethod
from z3 import Solver, RealVector

class Sender:
    def __init__(self, id):
        self.id = id
        self._params = set()
        self._vars = set()

    # Add parameters which will be made available via the '.' operator:
    # Eg. If we pass in params_dict={
    #   'param1': 10,
    # },
    # then self.param1 is set as 10.
    def add_params(self, params_dict):
        for param_name, param_val in params_dict.items():
            if param_name.startswith('_'):
                raise ValueError("Cannot overwrite internal variable!")
            self._params.add(param_name)
            setattr(self, param_name, param_val)

    # Print all of the parameters we've added.
    def print_params(self):
        print('Sender %s Parameters:' % self.id)
        for param in sorted(self._params, key=lambda param: param.lower()):
            print(' - %s: %s' % (param, getattr(self, param)))

    # Add constraint variables which will be made available via the '.' operator:
    # Eg. If we pass in vars_dict={
    #   'out': RealVector('out', sz=10),
    # },
    # then self.out is set as RealVector('out', sz=10).
    def add_constraint_vars(self, vars_dict):
        for var_name, var_val in vars_dict.items():
            if var_name.startswith('_'):
                raise ValueError("Cannot overwrite internal variable!")
            self._vars.add(var_name)
            setattr(self, var_name, var_val)

    # Print all of the variables we've added.
    def print_vars(self, brief=False):
        print('Sender %s Variables:' % self.id)
        for var in sorted(self._vars, key=lambda var: var.lower()):
            if brief:
                print(' - %s' % (var))
            else:
                print(' - %s: %s' % (var, getattr(self, var)))

class AbstractSMTNetworkModel(ABC):
    def __init__(self):
        super().__init__()
        self._solver = Solver()
        self._senders = {}
        self._global_params = set()
        self._global_vars = set()

    # Register a sender with the current model.
    def register_sender(self, sender):
        if sender.id in self._senders:
            raise ValueError('Sender already registered, or duplicate sender IDs used.')
        self._senders[sender.id] = sender

    # Register a list of senders.
    def register_senders(self, senders):
        for sender in senders:
            self.register_sender(sender)

    # Get a registered sender by ID.
    def get_sender(self, sender_id):
        return self._senders[sender_id]

    ## Parameters-related.
    # Add global parameters.
    def add_global_params(self, params_dict):
        for param_name, param_val in params_dict.items():
            if param_name.startswith('_'):
                raise ValueError("Cannot overwrite internal variable!")
            self._global_params.add(param_name)
            setattr(self, param_name, param_val)

    # Print global parameters that we've added.
    def print_global_params(self):
        print('Global Parameters:')
        if len(self._global_params) == 0:
            print(' (none)')

        for param in sorted(self._global_params, key=lambda param: param.lower()):
            print(' - %s: %s' % (param, getattr(self, param)))

    # Add parameters for a particular sender.
    def add_params_for_sender(self, params_dict, sender_id):
        self._senders[sender_id].add_params(params_dict)

    # Print parameters for a particular sender.
    def print_params_for_sender(self, sender_id):
        self._senders[sender_id].print_params()

    # Print ALL parameters.
    def print_all_params(self):
        for sender_id in self._senders:
            self.print_params_for_sender(sender_id)
        self.print_global_params()
        print()

    ## Constraint variables-related.
    # Add global constraint variables.
    def add_global_constraint_vars(self, vars_dict):
        for var_name, var_val in vars_dict.items():
            if var_name.startswith('_'):
                raise ValueError("Cannot overwrite internal variable!")
            self._global_vars.add(var_name)
            setattr(self, var_name, var_val)

    # Print global parameters that we've added.
    def print_global_vars(self, brief=False):
        print('Global Variables:')
        if len(self._global_vars) == 0:
            print(' (none)')

        for var in sorted(self._global_vars, key=lambda var: var.lower()):
            if brief:
                print(' - %s' % (var))
            else:
                print(' - %s: %s' % (var, getattr(self, var)))

    # Add variables used in constraints for a particular sender.
    def add_constraint_vars_for_sender(self, vars_dict, sender_id):
        self._senders[sender_id].add_constraint_vars(vars_dict)

    # Print variables for a particular sender.
    def print_vars_for_sender(self, sender_id, brief=False):
        self._senders[sender_id].print_vars(brief=brief)

    # Print ALL variables.
    def print_all_vars(self, brief=False):
        for sender_id in self._senders:
            self.print_vars_for_sender(sender_id, brief=brief)
        self.print_global_vars(brief=brief)
        print()

    ## Constraints-related.
    # Add a generic constraint.
    def add_constr(self, constr):
        self._solver.add(constr)

    ## Sender-wise constraints.
    # Constraints on the flow itself.
    @abstractmethod
    def add_flow_constraints_for_sender(self, sender_id):
        pass
    
    # Initial constraints on the variables.
    @abstractmethod
    def add_initial_constraints_for_sender(self, sender_id):
        pass

    # Additional constraints on the solution (such as no loss, max queueing delay, and so on).
    # This is optional.
    def add_additional_constraints_for_sender(self, sender_id):
        pass

    # Constraints that define the congestion control algorithm.
    @abstractmethod
    def add_congestion_control_for_sender(self, sender_id):
        pass
    
    # Add ALL constraints for a sender!
    def add_all_constraints_for_sender(self, sender_id):
        self.add_initial_constraints_for_sender(sender_id)
        self.add_flow_constraints_for_sender(sender_id)
        self.add_congestion_control_for_sender(sender_id)
        self.add_additional_constraints_for_sender(sender_id)

    ## Global constraints.
    # This is optional.
    def add_global_constraints(self):
        pass

    # Add ALL constraints for all senders!
    def add_all_constraints(self):
        for sender_id in self._senders:
            self.add_all_constraints_for_sender(sender_id)
        self.add_global_constraints()

    # Check if all constraints are satisfied.
    def check(self):
        return self._solver.check()
