#!/usr/bin/env python3
"""
Mathematical analysis of the constraint differential equation inconsistency.
"""

import numpy as np
import matplotlib.pyplot as plt

# Define the constraint accumulation function
def C(epsilon, gamma=1, epsilon_0=1):
    """C(ε) = γε(1 - e^(-ε/ε₀))"""
    return gamma * epsilon * (1 - np.exp(-epsilon / epsilon_0))

# Define the given ConstraintRate function
def ConstraintRate_given(epsilon, gamma=1, epsilon_0=1):
    """Given: ConstraintRate ε = γ(1 - e^(-ε/ε₀)) + γ(ε/ε₀)e^(-ε/ε₀)"""
    return gamma * (1 - np.exp(-epsilon / epsilon_0)) + gamma * (epsilon / epsilon_0) * np.exp(-epsilon / epsilon_0)

# Define what the theorem claims ConstraintRate should be
def ConstraintRate_theorem(epsilon, gamma=1, epsilon_0=1):
    """Theorem claims: ConstraintRate ε = γ(1 - C(ε)/(γε))"""
    if epsilon == 0:
        return 0  # Avoid division by zero
    return gamma * (1 - C(epsilon, gamma, epsilon_0) / (gamma * epsilon))

# Calculate the actual derivative of C(ε) numerically
def dC_depsilon(epsilon, gamma=1, epsilon_0=1):
    """Actual derivative dC/dε using numerical differentiation"""
    h = 1e-6
    return (C(epsilon + h, gamma, epsilon_0) - C(epsilon - h, gamma, epsilon_0)) / (2 * h)

# Test values
epsilon_values = np.linspace(0.1, 5, 100)

print("MATHEMATICAL INCONSISTENCY ANALYSIS")
print("=" * 50)

# Test at a specific point
eps_test = 1.0
print(f"\nAt epsilon = {eps_test}:")
print(f"C(epsilon) = {C(eps_test):.6f}")
print(f"Given ConstraintRate = {ConstraintRate_given(eps_test):.6f}")
print(f"Theorem claims ConstraintRate = {ConstraintRate_theorem(eps_test):.6f}")
print(f"Actual derivative dC/depsilon = {dC_depsilon(eps_test):.6f}")

# Check if ConstraintRate_given is actually the derivative of C
print(f"\nIs ConstraintRate_given the derivative of C?")
for eps in [0.5, 1.0, 2.0, 3.0]:
    given = ConstraintRate_given(eps)
    derivative_val = dC_depsilon(eps)
    print(f"  eps={eps}: Given={given:.6f}, Derivative={derivative_val:.6f}, Diff={abs(given-derivative_val):.8f}")

# Simplify the theorem's right-hand side algebraically
print(f"\nAlgebraic simplification of theorem's RHS:")
print(f"gamma(1 - C(eps)/(gamma*eps)) = gamma(1 - gamma*eps*(1-exp(-eps/eps0))/(gamma*eps))")
print(f"                              = gamma(1 - (1-exp(-eps/eps0)))")
print(f"                              = gamma(1 - 1 + exp(-eps/eps0))")
print(f"                              = gamma*exp(-eps/eps0)")

eps_test = 1.0
theorem_simplified = 1 * np.exp(-eps_test / 1)  # gamma*exp(-eps/eps0)
print(f"\nAt eps={eps_test}: Theorem simplified = {theorem_simplified:.6f}")
print(f"But ConstraintRate_given = {ConstraintRate_given(eps_test):.6f}")
print(f"These are clearly different!")

# What should the correct differential equation be?
print(f"\nCORRECT FORMULATION:")
print(f"If ConstraintRate is dC/deps, then the correct statement is:")
print(f"dC/deps = gamma(1 - exp(-eps/eps0)) + gamma(eps/eps0)exp(-eps/eps0)")
print(f"This is indeed the derivative of C(eps) = gamma*eps*(1 - exp(-eps/eps0))")

# Verify by taking the derivative analytically
print(f"\nAnalytical verification:")
print(f"C(eps) = gamma*eps*(1 - exp(-eps/eps0))")
print(f"dC/deps = gamma(1 - exp(-eps/eps0)) + gamma*eps * d/deps(1 - exp(-eps/eps0))")
print(f"        = gamma(1 - exp(-eps/eps0)) + gamma*eps * (1/eps0)*exp(-eps/eps0)")
print(f"        = gamma(1 - exp(-eps/eps0)) + gamma*(eps/eps0)*exp(-eps/eps0)")
print(f"This matches ConstraintRate_given exactly!")

# Suggest correct theorem statement
print(f"\nCORRECT THEOREM STATEMENT:")
print(f"theorem constraint_derivative (eps : Real) (h_pos : eps > 0) :")
print(f"  ConstraintRate eps = gamma * (1 - Real.exp (-eps / eps0)) + gamma * (eps / eps0) * Real.exp (-eps / eps0)")
print(f"  AND ConstraintRate eps = derivative_of C at eps := by")
print(f"  -- This would be provable by direct calculation")

print(f"\nOR ALTERNATIVELY:")
print(f"theorem constraint_differential_equation_correct (eps : Real) (h_pos : eps > 0) :")
print(f"  HasDerivAt C (ConstraintRate eps) eps := by")
print(f"  -- This states that ConstraintRate is the derivative of C")

print(f"\nThe original theorem with gamma(1 - C(eps)/(gamma*eps)) should be DELETED as it's mathematically false.")