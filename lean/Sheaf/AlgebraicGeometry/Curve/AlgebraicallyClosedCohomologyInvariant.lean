module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Algebraically closed extension for reduced proper curves

Source: Stacks Project, Theorem 03SC, item (7), and Lemmas 03SD, 0A3Q, 03SG.
(blueprint: e1-algebraically-closed-cohomology-invariant)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

/-- Field extension invariance for reduced proper curves with constructible prime coefficients.
Source: Stacks Theorem 03SC, item (7), after the reduction to constructible prime torsion;
Lemmas 03SD, 0A3Q and 03SG supply the locally constant and normalization steps.

Choose a dense open which is a finite disjoint union of irreducible opens on which `F` is
finite locally constant. Its complement is zero-dimensional. The open-closed exact sequence,
zero-dimensional field invariance, and the cohomology comparison ladder reduce the assertion
to each extension by zero of a finite locally constant sheaf of prime-field vector spaces.

On an irreducible open choose a connected finite etale cover of degree prime to `r` on which
the sheaf has a finite filtration with constant prime-field quotients. Unit followed by trace
is multiplication by the cover's degree, hence invertible; the original sheaf is a retract
of the pushforward. Compactify the cover by Zariski's main theorem to a finite map over the
curve, with the cover a dense open. The compactification may be reduced, and the inverse
image of the original open is the cover. Finite pushforward commutes with extension by zero.
Exactness of extension by zero and the long exact cohomology sequence reduce the filtration
to constant prime-field coefficients extended by zero on a reduced curve.

Normalize this curve. Normalization is finite and smooth, and an isomorphism on a dense open.
The two constructible sheaves, the original extension by zero and the pushforward from the
normalization, agree there. Dense-open localization and finite pushforward reduce to the
smooth case. Decompose the smooth curve into its finitely many connected components. Points
have only degree-zero cohomology and are invariant under algebraically closed extension.
For the one-dimensional components the smooth constant curve calculations give all eight
assertions, including proper field invariance, and dense-open localization gives the same
for extension by zero. Retracts, finite sums and short exact sequences preserve these
assertions. Reading off assertion C7 proves the displayed bijectivity in every degree.
The empty curve or zero sheaf has zero cohomology, so these cases cause no exception.
(blueprint: e1-algebraically-closed-cohomology-invariant) -/
theorem algebraicallyClosedCohomologyInvariant {k : Type u} [Field k] [IsAlgClosed k]
    {C C' : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsProper f] [IsReduced C]
    (k' : Type u) [Field k'] [IsAlgClosed k'] {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C} (h : IsPullback ι' f' f ι)
    {r : ℕ} [Fact r.Prime]
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    [Scheme.IsConstructibleSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
        AddCommGrpCat.{u + 1})).obj F) q) := by
  sorry

end AlgebraicGeometry.IsCurve
