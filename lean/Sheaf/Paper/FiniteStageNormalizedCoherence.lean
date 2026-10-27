/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F8
-/
module

public import Sheaf.Paper.FiniteCoefficientAdjointData

/-! # Coherence of normalized finite-stage comparisons

Source: current blueprint reduction-exceptional and field-extension towers,
parent node proof step 7 (projection cocycle and mate pasting).
(blueprint: lem-pur-finite-stage-normalized-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
attribute [local instance 20000] CommRing.toRing Field.toCommRing DFunLike.toCoeFun
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
namespace AlgebraicGeometry.FiniteCoefficientAdjoints

/-- Normalized individual adjunctions and coefficient comparisons satisfy composition,
identity, and compactification-refinement coherence.

Source: current blueprint reduction-exceptional and field-extension towers;
parent lem-pur-finite-coefficient-adjoint-comparisons, proof step 7.
(blueprint: lem-pur-finite-stage-normalized-coherence).

Proof: on a retained etale witness expand both coefficient composites using
projection_normalization. Naturality moves the witness isomorphisms through the
functors. The site/coefficient square cancels the middle site comparisons, and the
ringed coefficient projection cocycle identifies both remaining maps with the
extension to the composite coefficient ring of the same evaluation counit.
Open extension gives the same equation termwise by tensor balancing. This proves
projection_comp with the canonical scalar associators; the identity case gives
projection_id with normalizedOriginScalarUnit. Define the refinement lower iso by
transporting the specified ordinary etale proper/open refinement iso through the
site comparison. Naturality shows its value is refinementAtWitness, independently
of the witness. Its right-adjoint conjugate is the unique map with the stated
upper_normalization, hence an iso. The site/coefficient refinement square proves
projection_refinement. For mate_comp transpose the two proposed composites under
the final adjunction: substitute each Change.counit_equation and then use the
projection cocycle; both transposes are the scalar-extended initial counit preceded
by the inverse composite projection. Injectivity gives mate_comp. The same
argument with the scalar unit proves mate_id, and with the lower refinement
square proves mate_refinement. Normalized projection and conjugate counit fix both
refinement isomorphisms uniquely; proof irrelevance fixes their proof fields.
No compatibility hypotheses on the input families are required, since every
Change and AdjointDatum already carries the specified normalization. -/
theorem finite_stage_normalized_coherence
    (k : Type u) [Field k] (p l : ℕ) [CharP k p] (hp : 0 < p)
    [Fact l.Prime] (hlp : l ≠ p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] :
    letI := finiteTypeNoetherian k X
    letI := finiteTypeNoetherian k Y
    letI := (finiteTypeMorphismProperties k f).1
    letI := (finiteTypeMorphismProperties k f).2.1
    letI := (finiteTypeMorphismProperties k f).2.2
    ∀ (datum : ∀ (s : Stage l E) (c : Compactification f), AdjointDatum s.ring c)
      (change : ∀ {s t : Stage l E} (a : Arrow s t) (c : Compactification f),
    Change a.ringMap c (datum s c) (datum t c)),
      ∃! refinement : ∀ (s : Stage l E) {c d : Compactification f} (r : c.Refinement d),
    RefinementDatum r (datum s c) (datum s d),
        (∀ {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v)
    (ab : Arrow s v) (h : ab.embedding = b.embedding.comp a.embedding)
    (c : Compactification f) (K : (ctf s.ring X).FullSubcategory),
    (tensor b.ringMap Y).map ((change a c).projection.hom.app K) ≫
        (change b c).projection.hom.app
          ⟨(tensor a.ringMap X).obj K.obj,
            (change a c).tensor_preserves_X K.obj K.property⟩ ≫
        (lower v.ring c).map
          ((ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X)
            a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)).hom.app K.obj) =
      (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology Y)
          a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)).hom.app
            ((lower s.ring c).obj K.obj) ≫
        (change ab c).projection.hom.app K) ∧
        (∀ {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v)
    (ab : Arrow s v) (h : ab.embedding = b.embedding.comp a.embedding)
    (c : Compactification f) (K : (ctf s.ring Y).FullSubcategory),
    (tensor b.ringMap X).map ((change a c).mate.hom.app K) ≫
        (change b c).mate.hom.app
          ⟨(tensor a.ringMap Y).obj K.obj,
            (change a c).tensor_preserves_Y K.obj K.property⟩ ≫
        (upper v.ring c).map
          ((ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology Y)
            a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)).hom.app K.obj) =
      (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X)
          a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)).hom.app
            ((upper s.ring c).obj K.obj) ≫
        (change ab c).mate.hom.app K) ∧
        (∀ (s : Stage l E) (a : Arrow s s)
    (h : a.embedding = AlgHom.id (Padic l) s.field)
    (c : Compactification f) (K : (ctf s.ring X).FullSubcategory),
    (change a c).projection.hom.app K ≫
        (lower s.ring c).map ((ProEtale.normalizedOriginScalarUnit
          (Scheme.ProEt.topology X) a.ringMap (Arrow.ringMap_id a h)).hom.app K.obj) =
      (ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology Y)
        a.ringMap (Arrow.ringMap_id a h)).hom.app ((lower s.ring c).obj K.obj)) ∧
        (∀ (s : Stage l E) (a : Arrow s s)
    (h : a.embedding = AlgHom.id (Padic l) s.field)
    (c : Compactification f) (K : (ctf s.ring Y).FullSubcategory),
    (change a c).mate.hom.app K ≫
        (upper s.ring c).map ((ProEtale.normalizedOriginScalarUnit
          (Scheme.ProEt.topology Y) a.ringMap (Arrow.ringMap_id a h)).hom.app K.obj) =
      (ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology X)
        a.ringMap (Arrow.ringMap_id a h)).hom.app ((upper s.ring c).obj K.obj)) ∧
        (∀ {s t : Stage l E} (a : Arrow s t)
    {c d : Compactification f} (r : c.Refinement d) (K : (ctf s.ring X).FullSubcategory),
    (tensor a.ringMap Y).map ((refinement s r).lowerIso.hom.app K) ≫
        (change a d).projection.hom.app K =
      (change a c).projection.hom.app K ≫
        (refinement t r).lowerIso.hom.app
          ⟨(tensor a.ringMap X).obj K.obj, (change a c).tensor_preserves_X K.obj K.property⟩) ∧
        (∀ {s t : Stage l E} (a : Arrow s t)
    {c d : Compactification f} (r : c.Refinement d) (K : (ctf s.ring Y).FullSubcategory),
    (tensor a.ringMap X).map ((refinement s r).upperIso.hom.app K) ≫
        (change a c).mate.hom.app K =
      (change a d).mate.hom.app K ≫
        (refinement t r).upperIso.hom.app
          ⟨(tensor a.ringMap Y).obj K.obj,
            (change a c).tensor_preserves_Y K.obj K.property⟩) := by sorry

end AlgebraicGeometry.FiniteCoefficientAdjoints
