/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.Algebra.Homology.KFlatTensorQuasiIso
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Exact internal Hom from a projective module on the one-object site

Source: Stacks Project, more-algebra.tex, Tag 0A6A, bounded projective computation;
algebra.tex, projective modules and exactness of Hom.
(blueprint: lem-pc-ring-projective-internal-hom-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

/-- Internal Hom from a projective module on the one-object bottom-topology site
preserves short exact sequences. No finite-generation assumption is needed.
Source: Stacks Project, more-algebra.tex, Tag 0A6A, projective Hom computation;
algebra.tex, projective modules and exactness of Hom.
(blueprint: lem-pc-ring-projective-internal-hom-exact).

Proof: evaluation at the unique object identifies sheaves of modules on this site
with modules over A: there are only identity restriction maps, and the bottom topology
imposes no additional condition. The slice over the unique object is again this site,
so evaluation of the shared internal Hom is Hom_A(M(*),N(*)), with homObjMap acting
by pre- and postcomposition. A short exact sequence evaluates to a short exact
sequence of A-modules. Hom_A(M(*),-) preserves kernels, giving injectivity and
exactness at the middle term. Projectivity of M(*) lifts every map M(*) to the last
term through the surjection from the middle term, giving surjectivity. The composite
is zero since the original composite is zero. Evaluation reflects these three
properties, so the internal-Hom sequence is short exact. This also covers the zero
ring, the zero source, and projectives of infinite rank. -/
theorem ringProjectiveInternalHomExact {A : Type u} [CommRing A]
    (M : SheafOfModules.{u} ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (CochainComplex.onePointRingSheaf A)))
    (hM : Module.Projective A (M.val.obj (op ⟨PUnit.unit⟩)))
    (S : ShortComplex (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A)))) (hS : S.ShortExact) :
    ∃ hz : homObjMap (R := CochainComplex.onePointRingSheaf A) (𝟙 M) S.f ≫
        homObjMap (R := CochainComplex.onePointRingSheaf A) (𝟙 M) S.g = 0,
      (ShortComplex.mk
        (homObjMap (R := CochainComplex.onePointRingSheaf A) (𝟙 M) S.f)
        (homObjMap (R := CochainComplex.onePointRingSheaf A) (𝟙 M) S.g) hz).ShortExact := by
  sorry

end SheafOfModules
