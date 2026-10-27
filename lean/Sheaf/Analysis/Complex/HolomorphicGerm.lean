module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Topology.Germ
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Holomorphic germs at the origin

Source: Serre, GAGA, no.4, printed p.6: the complex algebra of holomorphic germs.
(blueprint: def-sfb-holomorphic-germ-algebra)

Total functions analytic at zero represent functions on a neighbourhood of zero.
The kernel of the map to Mathlib's neighbourhood germs identifies precisely
representatives that agree on a smaller neighbourhood. All algebra data are constructed.
-/

@[expose] public section

set_option autoImplicit false

open scoped Topology

namespace Complex

/-- Functions analytic at zero, with pointwise operations. Source: Serre, GAGA,
no.4, printed p.6; closure operations are Mathlib's analytic function operations.
(blueprint: def-sfb-holomorphic-germ-algebra) -/
noncomputable def analyticAtZeroSubalgebra (d : ℕ) :
    Subalgebra ℂ ((Fin d → ℂ) → ℂ) where
  carrier := {f | AnalyticAt ℂ f 0}
  mul_mem' := fun hf hg ↦ hf.mul hg
  add_mem' := fun hf hg ↦ hf.add hg
  algebraMap_mem' := fun _ ↦ analyticAt_const
  zero_mem' := analyticAt_const
  one_mem' := analyticAt_const

/-- The neighbourhood-germ map on analytic representatives. Source: Serre, GAGA,
no.4, printed p.6. Its kernel consists exactly of functions zero near zero.
(blueprint: def-sfb-holomorphic-germ-algebra) -/
noncomputable def analyticAtZeroGermMap (d : ℕ) :
    analyticAtZeroSubalgebra d →+* Filter.Germ (𝓝 (0 : Fin d → ℂ)) ℂ :=
  (Filter.Germ.coeRingHom _).comp (analyticAtZeroSubalgebra d).val.toRingHom

/-- The complex algebra of holomorphic germs at zero in `ℂ^d`. Source: Serre,
GAGA, no.4, printed p.6. Quotienting analytic representatives by the kernel of
Mathlib's germ map is exactly agreement on some open neighbourhood of zero.
(blueprint: def-sfb-holomorphic-germ-algebra) -/
noncomputable abbrev HolomorphicGerm (d : ℕ) :=
  analyticAtZeroSubalgebra d ⧸ RingHom.ker (analyticAtZeroGermMap d)

/-- The germ of an analytic representative. Source: Serre, GAGA, no.4, printed p.6.
(blueprint: def-sfb-holomorphic-germ-algebra) -/
noncomputable def holomorphicGermMk (d : ℕ) :
    analyticAtZeroSubalgebra d →ₐ[ℂ] HolomorphicGerm d :=
  Ideal.Quotient.mkₐ ℂ _

/-- Evaluation of a holomorphic germ at zero. Source: Serre, GAGA, no.4,
printed p.6. Evaluation of neighbourhood germs ensures well-definedness.
(blueprint: def-sfb-holomorphic-germ-algebra) -/
noncomputable def holomorphicGermValue (d : ℕ) : HolomorphicGerm d →ₐ[ℂ] ℂ where
  __ := Ideal.Quotient.lift _
    (Filter.Germ.valueRingHom.comp (analyticAtZeroGermMap d))
    (fun f hf ↦ by
      change Filter.Germ.valueRingHom (analyticAtZeroGermMap d f) = 0
      rw [RingHom.mem_ker.mp hf, map_zero])
  commutes' := fun _ ↦ rfl

/-- The coordinate germs. Source: Serre, GAGA, no.4, printed p.6.
(blueprint: def-sfb-holomorphic-germ-algebra) -/
noncomputable def holomorphicGermCoordinate (d : ℕ) (i : Fin d) : HolomorphicGerm d :=
  holomorphicGermMk d ⟨fun x ↦ x i,
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) i).analyticAt
      (0 : Fin d → ℂ)⟩

/-- The ideal of germs vanishing at zero. Source: Serre, GAGA, no.4, printed p.6.
(blueprint: def-sfb-holomorphic-germ-algebra) -/
noncomputable def holomorphicGermVanishingIdeal (d : ℕ) : Ideal (HolomorphicGerm d) :=
  RingHom.ker (holomorphicGermValue d)

end Complex
