module

public import Sheaf.AlgebraicGeometry.CohomologyFractionPresentation

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- If the degree-zero fraction presentation is zero, each global cohomology class
is killed by a tensor power of the section. This is only the denominator-clearing
step; it assumes neither an affine nonvanishing open nor a localization comparison.

Source: Stacks Project, Cohomology of Schemes, Lemma 01XR, conclusion from the
localization of Lemma 09MR (https://stacks.math.columbia.edu/tag/01XR).
(blueprint: lem-sc-section-affine-open-kills-cohomology-localization-step).

Proof: Forget the scalar action on module cohomology. Global module sections with
scalars forgotten are sections on the top open. Forgetting scalars is exact, so it
commutes with cohomology of an injective module resolution and gives a natural
additive isomorphism from global module cohomology to open module cohomology at top.
Transport xi through this isomorphism and through the map induced by the inverse
right unitor F -> F tensor L^0, obtaining a numerator eta in degree zero.
The hypothesis makes the fraction [0, eta] zero. The fraction presentation is the
additive direct limit of the groups H^p(X,F tensor L^n), with transitions induced
by mulTensorPowSection. These transitions compose because section powers multiply
and the tensor associators and unitors satisfy coherence. Its defining relations
are exactly the relations of cohomologyFractionRelations. In a directed colimit,
a component representing zero becomes zero at some later index e: equivalently,
write its relation as a finite sum of defining relations and push all terms to a
common index, where each relation cancels. Thus the transition from degree zero
to degree e kills eta. By the tensor coherence identities, its composite with the
inverse right unitor is (rho F).inv followed by F tensor s^e. Naturality of the
comparison with global module cohomology transports this equality back to the
claimed map applied to xi. -/
theorem exists_tensorPowSection_cohomology_eq_zero_of_subsingleton_fractions
    (X : Scheme.{u}) (L F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ)
    (hsub : Subsingleton (CohomologyFractionPresentation L F s p ⊤))
    (xi : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F) :
    ∃ e : ℕ, (RingedSpace.moduleCohomology X.toRingedSpace p).map
      ((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) e) xi = 0 := by
  sorry

end AlgebraicGeometry.Scheme.Modules
