module

public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Homeomorph.Lemmas

import Sheaf.RingTheory.IndEtaleStability
import Sheaf.Paper.CondensedPointBasis
import Sheaf.AlgebraicGeometry.SpecFiniteProductFields
import Sheaf.Topology.FilteredSpectrumTopologicalLimit
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Geometric fibres detect fpqc coverings over a field

Source: Bhatt--Scholze, Definition 4.1.1 and Example 4.1.10, pp. 27--28
(blueprint: lem-sfb-field-geometric-fibre-covering-test).

The two explicit topologies in the statement are the initial topologies for restriction
to every finite etale subalgebra, with discrete finite-stage Hom sets. No topology
on the coefficient field is substituted for these restriction topologies.
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.ProEtale

/-- Split base change identifies the geometric fibre with the spectrum, naturally,
and fpqc coverings are detected by a finite jointly surjective subfamily of fibres.
The residue-field clause uses bijectivity of the structural map from Ω, specifying
its canonical Ω-algebra identification. `AlgHom.liftEquiv` extends f by
`a ⊗ b ↦ a * f b`; its inverse is restriction along `b ↦ 1 ⊗ b`.
The kernel map is `PrimeSpectrum.comap` of this extension applied to the zero prime.
The two naturality equations specify contraction along `id ⊗ α` and restriction.

Source: Bhatt--Scholze, Definition 4.1.1 and Example 4.1.10, pp. 27--28
(blueprint: lem-sfb-field-geometric-fibre-covering-test).

Proof plan, following the eight DAG steps:
1. Ind-etale stability gives that Ω tensor B is ind-etale over Ω. By the finite
subalgebra construction and `condensed_point_basis`, each finite stage is Ω^n.
Contract a prime to each stage. The finite-product spectrum lemma shows its
quotient is Ω, so the structural map to the residue field is bijective.
2. At a finite split stage, homomorphisms to Ω are the coordinate projections,
with the discrete topology. Their kernels identify them with the spectrum.
The filtered-spectrum limit and the compatible-family construction identify
these inverse limits, giving the kernel homeomorphism over Ω.
3. Extension and restriction are inverse by the tensor universal property.
For continuity, any finite list of tensor generators involves only finitely
many elements of B; put them in one finite etale subalgebra. In the other
direction put the images of finitely many generators in one finite Ω-stage.
Compose extension with the kernel homeomorphism to obtain the displayed map.
4. Evaluate on pure tensors to check both naturality equations.
5. Ind-etale stability makes every arrow between the algebras weakly etale,
hence flat, including every member of the entire family.
6. For flat maps between affines, the fpqc definition is equivalent to finite
joint surjectivity on spectra. For the reverse implication, pull an affine open
back to affine fibre products and use that same finite subfamily.
7. An fpqc family has a finite covering subfamily. Base change along Spec Ω
preserves that cover. The affine fibre-product tensor identification and the
natural kernel homeomorphisms make its geometric fibres jointly surjective.
8. Conversely, lift a point of Spec B to Spec(Ω tensor B), using surjectivity
of the field extension and its base change. Joint surjectivity on the split
spectra lifts it to one source of the finite subfamily. Projecting back proves
joint surjectivity on Spec B, and step 6 applies. For B = 0 all spaces are empty
and the empty subfamily works; for B nonzero the fibre is nonempty, so an empty
family fails both tests. Zero sources contribute empty spaces. The same proof
works for k = Ω, with Ω its own separable closure. -/
theorem field_geometric_fibre_covering_test
    (k : Type u) (Ω : Type v) (B : Type w) [Field k] [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω] [CommRing B] [Algebra k B]
    (hB : RingHom.IndEtaleAcrossUniverses (algebraMap k B)) :
    RingHom.IndEtaleAcrossUniverses (algebraMap Ω (Ω ⊗[k] B)) ∧
    (∀ q : PrimeSpectrum (Ω ⊗[k] B),
      Function.Bijective (algebraMap Ω q.asIdeal.ResidueField)) ∧
    @IsHomeomorph (B →ₐ[k] Ω) (PrimeSpectrum (Ω ⊗[k] B))
      (⨅ (D : Subalgebra k B) (_ : Module.Finite k D) (_ : Algebra.Etale k D),
        TopologicalSpace.induced (fun f : B →ₐ[k] Ω ↦ f.comp D.val) ⊥)
      inferInstance (fun f ↦
        PrimeSpectrum.comap ((AlgHom.liftEquiv k Ω B Ω) f).toRingHom ⊥) ∧
    @IsHomeomorph ((Ω ⊗[k] B) →ₐ[Ω] Ω) (B →ₐ[k] Ω)
      (⨅ (D : Subalgebra Ω (Ω ⊗[k] B)) (_ : Module.Finite Ω D) (_ : Algebra.Etale Ω D),
        TopologicalSpace.induced (fun f : (Ω ⊗[k] B) →ₐ[Ω] Ω ↦ f.comp D.val) ⊥)
      (⨅ (D : Subalgebra k B) (_ : Module.Finite k D) (_ : Algebra.Etale k D),
        TopologicalSpace.induced (fun f : B →ₐ[k] Ω ↦ f.comp D.val) ⊥)
      (AlgHom.liftEquiv k Ω B Ω).symm ∧
    (∀ (D : Type w) [CommRing D] [Algebra k D],
      RingHom.IndEtaleAcrossUniverses (algebraMap k D) → ∀ α : B →ₐ[k] D,
      (∀ f : D →ₐ[k] Ω,
        PrimeSpectrum.comap ((AlgHom.liftEquiv k Ω B Ω) (f.comp α)).toRingHom ⊥ =
          PrimeSpectrum.comap (Algebra.TensorProduct.map (AlgHom.id Ω Ω) α).toRingHom
            (PrimeSpectrum.comap ((AlgHom.liftEquiv k Ω D Ω) f).toRingHom ⊥)) ∧
      (∀ h : (Ω ⊗[k] D) →ₐ[Ω] Ω,
        (AlgHom.liftEquiv k Ω B Ω).symm
            (h.comp (Algebra.TensorProduct.map (AlgHom.id Ω Ω) α)) =
          ((AlgHom.liftEquiv k Ω D Ω).symm h).comp α)) ∧
    (∀ (I : Type t) (Ba : I → Type w) [∀ a, CommRing (Ba a)] [∀ a, Algebra k (Ba a)]
      (α : ∀ a, B →ₐ[k] Ba a),
      (∀ a, RingHom.IndEtaleAcrossUniverses (algebraMap k (Ba a))) →
      (Presieve.ofArrows (fun a ↦ Spec (.of (Ba a)))
          (fun a ↦ Spec.map (CommRingCat.ofHom (α a).toRingHom)) ∈
        Scheme.fpqcPrecoverage (Spec (.of B)) ↔
      ∃ J : Finset I, ∀ f : B →ₐ[k] Ω,
        ∃ a ∈ J, ∃ g : Ba a →ₐ[k] Ω, g.comp (α a) = f)) := by
  sorry

end AlgebraicGeometry.ProEtale
