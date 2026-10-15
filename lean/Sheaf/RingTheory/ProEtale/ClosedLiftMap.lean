/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import WeilConjectures.RingTheory.ProEtale.ClosedLift
public import Sheaf.RingTheory.IndPrincipalZariski
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.FinitePresentation

/-! # Functoriality of the ind-etale closed lift

Source: blueprint, smooth purity, `sk-prop-sf-open-closed-triangle`,
`def-exc-ind-etale-closed-lift` (blueprint: def-exc-ind-etale-closed-lift).

The indexing category, diagram, colimit algebra and retained map are the existing
`Algebra.ClosedLift.Index`, `diagram`, `Algebra.ClosedLift` and `toAlgHom`.
This module supplies postcomposition and the resulting map of colimits.
The construction applies to arbitrary input algebras; in particular it applies to
ind-etale algebras over `A ⧸ I`, with their induced `A`-algebra structures.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Algebra.ClosedLift

variable {A C C' : Type u} [CommRing A] [CommRing C] [CommRing C']
  [Algebra A C] [Algebra A C']

/-- The retained map to the input algebra is induced by the factorization maps.
Source: blueprint `def-exc-ind-etale-closed-lift`, second paragraph
(blueprint: def-exc-ind-etale-closed-lift).
Proof: the defining colimit descent satisfies `colimit.ι_desc` at every index. -/
theorem ι_toAlgHom (X : Index A C) :
    (toAlgHom A C).comp (colimit.ι (diagram A C) X).hom = X.toC := sorry

/-- Postcomposition preserves compatibility with the input algebra map.
Source: blueprint `def-exc-ind-etale-closed-lift`, final sentence
(blueprint: def-exc-ind-etale-closed-lift).
Proof: associate the three algebra maps and substitute `f.comp_toC`. -/
theorem postcomp_compatible (φ : C →ₐ[A] C') {X Y : Index A C} (f : X ⟶ Y) :
    (φ.comp Y.toC).comp f.hom = φ.comp X.toC := sorry

/-- Postcomposition on the small indexing categories, leaving all underlying algebra maps
unchanged. Source: blueprint `def-exc-ind-etale-closed-lift`, final sentence
(blueprint: def-exc-ind-etale-closed-lift). -/
noncomputable def postcomp (φ : C →ₐ[A] C') : Index A C ⥤ Index A C' where
  obj X := ⟨X.n, X.rel, X.etale, φ.comp X.toC⟩
  map f := ⟨f.hom, postcomp_compatible φ f⟩

/-- The map of closed lifts induced by the cocone with components indexed by `(B, φ ∘ q)`.
Source: blueprint `def-exc-ind-etale-closed-lift`, final sentence
(blueprint: def-exc-ind-etale-closed-lift). -/
noncomputable def map (φ : C →ₐ[A] C') : ClosedLift A C →ₐ[A] ClosedLift A C' :=
  (colimit.desc (diagram A C)
    ((colimit.cocone (diagram A C')).whisker (postcomp φ))).hom

/-- The structure maps characterize the induced map of closed lifts.
Source: blueprint `def-exc-ind-etale-closed-lift`, final displayed equation
(blueprint: def-exc-ind-etale-closed-lift).
Proof: apply the factorization identity `colimit.ι_desc` to the defining cocone. -/
theorem ι_map (φ : C →ₐ[A] C') (X : Index A C) :
    (map φ).comp (colimit.ι (diagram A C) X).hom =
      (colimit.ι (diagram A C') ((postcomp φ).obj X)).hom := sorry

end Algebra.ClosedLift
