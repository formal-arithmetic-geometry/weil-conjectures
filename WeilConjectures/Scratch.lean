module

public import WeilConjectures.Blowup.EliminationOfIndeterminacy

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits HomogeneousLocalization
namespace AlgebraicGeometry
open AffineSpace

example {X : Scheme.{u}} [IsAffine X] (r : Γ(X, ⊤)) :
    algebraMap Γ(X, ⊤) Γ((X.basicOpen r).toScheme, ⊤) = (X.basicOpen r).ι.appTop.hom := rfl


end AlgebraicGeometry
