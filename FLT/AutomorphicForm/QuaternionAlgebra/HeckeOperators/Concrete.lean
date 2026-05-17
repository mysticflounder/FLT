/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Andrew Yang, Matthew Jasper, Adam McKenna
-/
module

public import FLT.AutomorphicForm.QuaternionAlgebra.HeckeOperators.Concrete.GoodPrime
public import FLT.AutomorphicForm.QuaternionAlgebra.HeckeOperators.Concrete.BadPrime
public import FLT.AutomorphicForm.QuaternionAlgebra.HeckeOperators.Concrete.HeckeAlgebra

/-!
# Concrete Hecke operators on quaternionic automorphic forms

Umbrella file: re-exports the concrete Hecke operator setup. Sub-files:

* `Concrete/GoodPrime.lean` — level subgroup `U₁(S)`, finiteness, `T_v` operator at
  good primes (`v ∉ S`) and the supporting `HeckeOperator.GoodPrime.*` scaffolding.
* `Concrete/BadPrime.lean` — `U_{v,α}` operator at bad primes (`v ∈ S`) and the
  cross-prime commutation lemmas (in `HeckeOperator.Internal`).
* `Concrete/HeckeAlgebra.lean` — `HeckeAlgebra F D r S R` and its `CommRing` instance.
-/
