module
public import Sheaf.FieldTheory.BrauerScalarDefect

@[expose] public section
universe u
namespace Field

/-- A jointly locally constant scalar two-cocycle has a homogeneous realization.
Proof: set f(g₀,g₁,g₂) = g₀(c(g₀⁻¹g₁,g₁⁻¹g₂)) and write its values
additively using Additive.ofMul. The action on each fixed unit is locally
constant, since the unit is algebraic and its stabilizer is Krull-open.
Together with joint local constancy of c and continuous group operations,
this makes f jointly continuous into the discrete coefficient module.
The absolute Galois group is compact Hausdorff, so the compact-open exponential
law curries f into the iterated continuous-map object in degree two.
Left translation of all three coordinates applies that same translation to
f, placing it in the invariant homogeneous cochains. At four coordinates,
put g = g₀⁻¹g₁, h = g₁⁻¹g₂ and k = g₂⁻¹g₃. The given identity, acted on
by g₀, is exactly the vanishing alternating homogeneous differential.
Lift this closed cochain along the kernel inclusion to obtain z. Evaluation
at (1,g,gh) is c(g,h), proving the requested equality. Normalization is unused.
Source: Stacks Project, Section 0DVG, homogeneous and inhomogeneous cochains.
(blueprint: lem-sc-brauer-scalar-defect-cocycle-realization). -/
theorem exists_galoisUnits_cocycle_of_scalar_cocycle (K : Type u) [Field K]
    (c : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
      (SeparableClosure K ≃ₐ[K] SeparableClosure K) → (SeparableClosure K)ˣ)
    (hlc : IsLocallyConstant (Function.uncurry c))
    (hc : ∀ g h k, c g h * c (g * h) k =
      g (c h k) * c g (h * k)) :
    ∃ z : ContinuousCohomology.cocycles (galoisUnitsTopRep K) 2,
      ∀ g h, galoisUnitsCocycleValue K z g h = c g h := by sorry
end Field
