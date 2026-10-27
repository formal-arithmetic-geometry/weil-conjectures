/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Sheaf.AlgebraicGeometry.GroupScheme.StandardProjectiveLinearAction
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.AlgebraicGeometry.Limits

import Sheaf.AlgebraicGeometry.GroupScheme.GeneralBorelFlagVariety
import Sheaf.AlgebraicGeometry.GroupScheme.SmoothGroupOrbitGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry
import Sheaf.RingTheory.SmoothAlgebraReduced
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Sheaf.AlgebraicGeometry.GroupScheme.BorelMaximalTorusConjugacy
import Sheaf.AlgebraicGeometry.GmRepresentationWeightBasis
import Sheaf.AlgebraicGeometry.TorusFixedSchemeSmooth
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-! # A linear one-parameter action with isolated fixed points on a general flag quotient

Source: Milne, Algebraic Groups (2017), Theorem 4.27, pp.94--95; Section 17f,
pp.368--369; Theorem 13.1, p.254; Lemma 13.51, pp.274--275; Theorem 17.65, p.374.
(blueprint: lem-sfb-general-flag-isolated-linear-action)

The nonzero vector space is F^(n+1), using a lifted finite coordinate index.
A basis identifies every nonzero finite-dimensional representation with such a model.
The quotient presentation and its action are fixed on generators of the coset presheaf.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped MonObj

namespace AlgebraicGeometry

/-- Every general Borel quotient admits a linear projective embedding and a cocharacter
whose fixed subscheme is a nonempty finite disjoint union of reduced rational points.
No reductivity or nontriviality of the cocharacter is assumed. The coordinate action
is the standard action on lines, specified on the complete homogeneous coordinate ring.
The fixed-functor condition includes every algebra extension, including nonreduced algebras.

Source: Milne, Theorem 4.27, pp.94--95; Theorem 17.9(a), p.354; Section 17f,
pp.368--369; Theorem 13.1, p.254; Lemma 13.51, pp.274--275; Theorem 17.65, p.374.
(blueprint: lem-sfb-general-flag-isolated-linear-action)

Proof, following the nine steps of the node:
1. The general Borel flag variety has stabilizer B and all rational points lie in its
   orbit. The smooth-group orbit lemma makes the reduced orbit locally closed. The
   closed-point residue-field and Jacobson lemmas show its complement is empty.
   Smoothness over the reduced field implies reducedness by the smooth-algebra lemma.
   The homogeneous-orbit quotient lemma identifies this orbit equivariantly with Q.
   Thus Q is smooth, connected, proper and finite type, and its points label Borels.
2. The Chevalley scheme-line-stabilizer lemma gives a nonzero finite-dimensional
   representation with line stabilizer B. The smooth-orbit and homogeneous-quotient
   lemmas identify its locally closed projective orbit with Q, on every test algebra.
3. Projective space is separated. The proper-over-separated lemma makes the immersion
   proper. It is a monomorphism, so the proper-monomorphism-closed lemma makes it closed.
4. The Borel maximal-torus conjugacy lemma supplies T in B, allowing rank zero.
   By the general flag lemma its fixed rational points are the Borels containing T.
   Torus-normalizer Borel transitivity and centralizer containment make these a quotient
   of the finite normalizer/centralizer group of the torus-normalizer-components lemma.
   There is at least one such Borel, namely B itself.
5. Repeatedly apply the Gm representation weight-basis lemma to the commuting split
   factors of T. Each factor preserves the previous weight spaces, giving a simultaneous
   weight decomposition. In rank zero the sole weight space is the whole vector space.
6. The projective-torus-fixed-weight-schemes lemma supplies a separating cocharacter
   and a common ambient fixed scheme for T and that cocharacter. Pull it back along
   the closed embedding to represent both fixed functors of Q. Eigenbasis charts
   give a finite invariant affine open cover, using the closed-immersion definition.
7. The open-immersion smooth-composition lemma makes each chart smooth. The torus
   fixed-scheme smoothness lemma makes its fixed scheme smooth. Smoothness is local
   on the source, so the common fixed scheme is smooth over F.
8. The fixed scheme is finite type. The residue-field and Jacobson lemmas identify its
   closed points with its finite nonempty rational-point set and show these exhaust it.
   This finite discrete topological space has dimension zero.
9. Regard it as the represented algebraic space. The zero-dimensional field-space
   components lemma gives finitely many nonempty Artinian one-point components.
   Smooth-over-field regularity and the regular-scheme definition make each dimension-zero
   local ring a field; its residue field is F. The components are therefore Spec F.
   If G=B the quotient is one point, and the cocharacter may be trivial. -/
theorem exists_general_flag_isolated_linear_action
    {F : Type u} [Field F] [IsAlgClosed F]
    (G B : Over (Spec (.of F))) [GrpObj G] [GrpObj B]
    [Smooth G.hom] [ConnectedSpace G.left] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (iB : B ⟶ G) (hB : IsBorelGroupScheme iB)
    (Q : Over (Spec (.of F))) [ModObj G Q] (q : G ⟶ Q)
    (ηQ : coequalizer (yoneda.map (fst G B))
      (yoneda.map (lift (fst G B) (snd G B ≫ iB) ≫ μ[G])) ⟶ yoneda.obj Q)
    (hηq : coequalizer.π _ _ ≫ ηQ = yoneda.map q)
    (hηQ : ∀ Z : Sheaf (Scheme.fppfTopology.over (Spec (.of F))) (Type u),
      Function.Bijective (fun f : yoneda.obj Q ⟶ Z.obj ↦ ηQ ≫ f))
    (hq : μ[G] ≫ q = (𝟙 G ⊗ₘ q) ≫ γ[G, Q]) :
    ∃ (n : ℕ) (ρ : G ⟶ GeneralLinearGroup (ULift.{u} (Fin (n + 1))) F),
      IsMonHom ρ ∧
      ∃ a : ModObj (GeneralLinearGroup (ULift.{u} (Fin (n + 1))) F)
          (linearProjectiveSpace F (ULift.{u} (Fin (n + 1)))),
        IsStandardProjectiveLinearAction F (ULift.{u} (Fin (n + 1))) a ∧
        ∃ j : Q ⟶ linearProjectiveSpace F (ULift.{u} (Fin (n + 1))),
          IsClosedImmersion j.left ∧
          γ[G, Q] ≫ j = (ρ ⊗ₘ j) ≫ a.smul ∧
          ∃ cochar : StandardGroupSchemes.multiplicative F ⟶ G,
            IsMonHom cochar ∧ ∃ (H : Over (Spec (.of F))) (jH : H ⟶ Q),
              IsClosedImmersion jH.left ∧
              (∀ (A : CommAlgCat.{u} F) (x : (algSpec (.of F)).obj (op A) ⟶ Q),
                (∃ z : (algSpec (.of F)).obj (op A) ⟶ H, z ≫ jH = x) ↔
                  ∀ (A' : CommAlgCat.{u} F) (f : A ⟶ A')
                    (t : (algSpec (.of F)).obj (op A') ⟶
                      StandardGroupSchemes.multiplicative F),
                    (t ≫ cochar) • ((algSpec (.of F)).map f.op ≫ x) =
                      (algSpec (.of F)).map f.op ≫ x) ∧
              ∃ r : ℕ, Nonempty (H ≅ ∐ fun _ : Fin (r + 1) ↦ 𝟙_ (Over (Spec (.of F)))) := by
  sorry

end AlgebraicGeometry
