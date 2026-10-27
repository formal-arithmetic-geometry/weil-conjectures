## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralVarietySmoothCurveInterpolation` states
`AlgebraicGeometry.Scheme.Hom.exists_smooth_connectedCurve_interpolating` with one `sorry`.
No definitions, additional nodes, dependency repairs, or mathematical statement corrections
are needed. The copied item changes only `lean`.

Source read: Charles--Poonen, *Bertini irreducibility theorems over finite fields*, printed
page 4, Theorem 1.8 and Corollary 1.9, from the local PDF. Corollary 1.9 gives the integral
curve through the closed points in positive dimension; normalization and the constant-map
zero-dimensional case are the assembled consequence explicitly recorded by the DAG node.
The recorded source and proof, including Stacks 0BXR, 0BX2 and 038X, are retained.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Algebraically closed field: `{k : Type u} [Field k] [IsAlgClosed k]`.
- Scheme integral over k: `{X : Scheme.{u}} [IsIntegral X]`, with structure morphism
  `(f : X ⟶ Spec (.of k))`. Mathlib's `IsIntegral` includes nonemptiness and precisely the
  integral-domain condition on nonempty opens, equivalent to the affine-open definition.
- Separated: `[IsSeparated f]`, defined by a closed-immersion diagonal.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the recorded conjunction.
- Finite nonempty set of k-rational points: `(F : Set (f.fieldPoints k))`, `(hF : F.Finite)`
  and `(hne : F.Nonempty)`. `fieldPoints` consists of sections of f: its equation uses
  `Spec.map (algebraMap k k)`, equal to the identity for the canonical self-algebra.
- Existence of a k-scheme D: `∃ (D : Scheme.{u}) (p : D ⟶ Spec (.of k))`.
- Separated, finite type, nonempty connected and dimension exactly one:
  `IsConnectedCurve p`. Its parent `IsCurve` contains `IsSeparated`, `LocallyOfFiniteType`
  and `QuasiCompact`; its fields are `ConnectedSpace D` and `topologicalKrullDim D = 1`.
  `ConnectedSpace` includes nonemptiness and absence of a nontrivial open partition.
- Smooth over k: `Smooth p`.
- k-morphism to X: `∃ (g : D ⟶ X), g ≫ f = p ∧ ...`.
- One rational point for every s in F: `∃ d : F → p.fieldPoints k, ...`. Here `F` is the
  subtype of the marked set, so the indexing is exactly by its members. The existing
  rational-point type supplies each section equation; no arbitrary bare point is substituted.
- All interpolation equations: `∀ s : F, (d s).val ≫ g = s.val.val`.
- The node's negative qualifications are respected: X has no positive-dimension,
  smoothness, properness or quasi-projectivity assumption; g has no immersion condition.

Existing dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs; `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic, for def-weil-field and the algebraically closed
  clause of def-weil-algebraic-closure. The latter node's `mathlib_match.how` explicitly
  identifies `IsAlgClosed`; choosing an algebraic closure of another field is unnecessary.
- `AlgebraicGeometry.Scheme` and scheme morphisms, Mathlib.AlgebraicGeometry.Scheme.
- `AlgebraicGeometry.IsIntegral`, Mathlib.AlgebraicGeometry.Properties.
- `AlgebraicGeometry.LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  and `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `AlgebraicGeometry.Scheme.Hom.fieldPoints`, publicly supplied by the recorded
  WeilConjectures.AlgebraicGeometry.DensePoints. The recorded
  `AlgebraicGeometry.Scheme.Hom.baseChangeFieldPoint` declaration and docstring were read;
  it uses exactly this existing rational-point type. Its full underlying definition is in
  lean/Comparator/Weil/Definitions.lean (module Weil.Definitions). There is no replacement
  rational-point definition in this delivery.
- `AlgebraicGeometry.IsCurve` and `AlgebraicGeometry.IsConnectedCurve`,
  WeilConjectures.AlgebraicGeometry.Curve; both full class signatures and docstrings read.
- `AlgebraicGeometry.Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `topologicalKrullDim`, Mathlib.Topology.KrullDimension, used by IsConnectedCurve's exact
  dimension field, with codomain `WithBot ℕ∞`.

All recorded modules of stated proof dependencies are imported plainly: finite-dimensionality
of finite-type schemes (WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType),
projective-line genus zero (Sheaf.AlgebraicGeometry.ProjectiveLineGenusZero), separated and
proper morphisms (Mathlib.AlgebraicGeometry.Morphisms.Separated and .Proper), finite morphisms
(Mathlib.AlgebraicGeometry.Morphisms.Finite), normalization and its existence/properties
(WeilConjectures.Mathlib.AlgebraicGeometry.Normalization), and smoothness of normalized curves
(WeilConjectures.AlgebraicGeometry.Regular). The Bertini dimension-cut node currently has no
Lean declaration, so there is no module for it to import; it is needed only by the future
proof, not by this statement. The six-step natural-language proof in the theorem docstring
tracks every step of the item's proof, including this prerequisite.

Edge cases checked before writing: X of dimension zero admits the constant projective-line
map and is included; X already an integral singular curve is handled by normalization;
marked points can be singular or multibranch, since only a lift is required. A singleton F
is included; empty F is excluded exactly by the node. Empty X is excluded by integrality.
Arbitrary finite sets, every characteristic, and arbitrary universe u are covered. The
shared universe is the existing scheme/field-point API convention and adds no dimension or
cardinality hypothesis. No smoothness or quasi-projectivity of X is inferred from the
conclusion. A family d indexed by F is equivalent by choice to the simultaneous finite
rational lifts requested by the node.

Searches actually performed with msearch.py (raw machine output is in searches.jsonl):

- LeanFinder: "Any finite nonempty set of rational points on an integral separated variety
  over an algebraically closed field lifts to a smooth connected curve". Eight hits,
  concerning Weierstrass models and points; none states the interpolation theorem.
- Loogle: "AlgebraicGeometry.IsIntegral, AlgebraicGeometry.IsCurve". The external index
  does not know the project's IsCurve, so this search is unavailable for that identifier;
  this is not treated as a negative match.
- Loogle: "AlgebraicGeometry.Smooth, AlgebraicGeometry.IsIntegral". Zero hits.
- LeanSearch: "Every finite set of rational points on an integral variety over an
  algebraically closed field lifts to a smooth connected curve". Eight hits on smooth
  morphisms, formally smooth lifts and Weierstrass points, none on the requested theorem.
- Mathlib grep via msearch.py: "curveThrough|curve_through|Bertini|bertini|interpol" in
  AlgebraicGeometry. Zero hits.
- Direct rg in WeilConjectures and Sheaf: "interpol|Bertini|bertini|curveThrough|curve_through"
  and searches for smooth connected curves and the item id. Read the plausible upstream
  WeilConjectures.AlgebraicGeometry.Bertini: its closed-curve theorem assumes a smooth affine
  geometric fibre over a finite field and a finite etale cover, so it does not state this
  theorem on arbitrary integral varieties. Other hits concern linear interpolation,
  relative curve models or separate Bertini incidence constructions. No existing match.
- Read dag/lean_names_upstream.json matches for curves/normalization. No binding of the
  requested interpolation theorem. The example CompactObject module is now withdrawn;
  read its current upstream module and node attachment for the actual header conventions.

No STATEMENT-DISPUTED issue or other mathematical node fault was found.

Validation: scompile.py compiled both the sandbox and the delivered library module cleanly
on the server (46.3 s and 15.1 s), with autoImplicit disabled and no diagnostic commands.

## Second reading by O3

A separate pass by this same dispatched worker re-read the node statement, the full existing
IsConnectedCurve and fieldPoints definitions, and the final theorem signature. The dispatcher
explicitly prohibits starting another agent; this is a self-review, not an assertion of an
independent second worker's review. The maintainer supplies the independent delivery review.

The important checks were that `IsCurve` alone would only bound dimension above by one and
permit the empty scheme, while `IsConnectedCurve` supplies the node's nonempty connectedness
and exact dimension; that rational points are sections rather than arbitrary morphisms from
Spec k; and that `g ≫ f = p` is necessary to say g is a k-morphism. All three are rendered in
the final signature. The outer subtype value picks a member of F and its inner value picks
its scheme morphism; hence the final equality is the exact interpolation equation. The
conclusion imposes no immersion condition on g, preserving the constant-map case. No mismatch
requiring a change was found in this pass.
