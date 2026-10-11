/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.IsFlasqueHomObjOfInjective
public import Sheaf.Topology.RingedSpaceModuleCohomology

/-! # Acyclicity of internal Hom into an injective module

Source: Stacks Project, Derived Categories of Varieties, Tag 0FZ3, proof of (1),
the local-to-global Ext spectral sequence input; Cohomology, Section 20.43,
and Tag 01EA (blueprint: lem-sc-ext-coherent-hom-injective-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Positive-degree cohomology of internal Hom from a coherent module to an injective module
vanishes.
Source: Stacks Project, Derived Categories of Varieties, Tag 0FZ3, proof of (1),
the local-to-global Ext spectral sequence input; Cohomology, Section 20.43,
and Tag 01EA (blueprint: lem-sc-ext-coherent-hom-injective-acyclic).

Proof:
1. By `lem-sc-ext-coherent-hom-injective-flasque`, the underlying abelian sheaf of
   `SheafOfModules.homObj F I` is flasque: injectivity extends morphisms along the
   monomorphism between extensions by zero of the restrictions of `F` to nested opens.
2. Apply `lem-sc-zariski-flasque-acyclic` to that underlying abelian sheaf. Its Zariski
   cohomology vanishes in every positive degree.
3. By `lem-sc-module-abelian-zariski-cohomology`, module cohomology has the same underlying
   abelian group as this Zariski cohomology. It therefore vanishes in every degree `p > 0`.
-/
theorem coherent_hom_injective_acyclic (X : Scheme.{u}) [IsNoetherian X]
    (F I : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) [Injective I] :
    ∀ p : ℕ, 0 < p →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj
        (SheafOfModules.homObj (R := X.sheaf) F I)) := by
  sorry

end AlgebraicGeometry
