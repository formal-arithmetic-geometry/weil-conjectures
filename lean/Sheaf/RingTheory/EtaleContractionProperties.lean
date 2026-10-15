/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.RingTheory.EtaleContraction
public import Sheaf.RingTheory.IndPrincipalZariski
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import Sheaf.Paper.EtaleFiniteDataDescent
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.RingTheory.ProEtale.RetractionsStrictlyHenselian
import Sheaf.RingTheory.DirectedColimitFaithfullyFlatAlgebras

/-!
# Properties of the étale contraction

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange, order 1227;
Stacks Project, proetale.tex, lemma-first-construction and Tag 097V
(blueprint: lem-weil-pbc-etale-contraction).
-/

@[expose] public section

universe u

namespace CommRingCat

/-- The canonical map to the étale contraction is faithfully flat and ind-étale;
faithfully flat étale algebras of finite presentation over it admit a section,
and its maximal localizations are strictly henselian.
Source: blueprint order 1227; Stacks, lemma-first-construction and Tag 097V
(blueprint: lem-weil-pbc-etale-contraction).

Proof plan:
1. Each chosen factor is faithfully flat. Tensor base change and composition preserve
faithful flatness, by the tensor identities on complexes, so all finite tensors and their
transition maps are faithfully flat, including the empty tensor.
2. Apply lem-weil-pbc-directed-colimit-faithfully-flat-algebras to finite-subset colimits
and then the sequential colimit. Apply lem-weil-pbc-ind-etale-stability to finite tensors,
base changes, compositions and these filtered colimits to get ind-étaleness.
3. An étale finitely presented algebra over the contraction descends to a stage by
lem-weil-pbc-etale-finite-data-descent. Use lem-weil-pbc-limit-affine-transition and
lem-weil-pbc-limit-affine-stage to make the model affine; its quasi-compactness and
quasi-separatedness and affine transitions follow from
lem-weil-pbc-affine-morphism-permanence. Faithful flatness descends by applying the
faithfully flat stage-to-colimit extension to complexes and the tensor identities.
4. The descended algebra is isomorphic to a chosen representative. Its singleton tensor
factor maps into the next stage and hence into the contraction. The tensor universal
property (lem-weil-pbc-algebra-tensor-base-change-universal-property) gives the retraction
by sending s ⊗ b to s h(b).
5. Every étale map of affine spectra is of finite presentation, since it is locally so
and affine maps are quasi-compact and quasi-separated. Thus the section property applies
to all faithfully flat étale algebras. Apply
lem-weil-pbc-split-etale-covers-maximal-local-criterion (Tag 097V) to each maximal ideal.
-/
theorem etaleContraction_properties (R : CommRingCat.{u}) :
    (EtaleContraction.ι R 0).hom.FaithfullyFlat ∧
    (EtaleContraction.ι R 0).hom.IndEtale ∧
    (∀ (B : Type u) [CommRing B] [Algebra R.etaleContraction B],
      Module.FaithfullyFlat R.etaleContraction B →
      Algebra.Etale R.etaleContraction B →
      Algebra.FinitePresentation R.etaleContraction B →
      Nonempty (B →ₐ[R.etaleContraction] R.etaleContraction)) ∧
    (∀ (m : Ideal R.etaleContraction) [m.IsMaximal],
      IsStrictlyHenselianLocalRing (Localization.AtPrime m)) := by
  sorry

end CommRingCat
