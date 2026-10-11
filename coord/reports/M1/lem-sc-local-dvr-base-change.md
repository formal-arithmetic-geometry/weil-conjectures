## Worker report

The module `Sheaf.AlgebraicGeometry.LocalDvrBaseChange` states
`AlgebraicGeometry.Scheme.local_dvr_base_change`, with its sole proof `sorry`.
The node copy changes only `lean`; no new nodes, dependency modules or statement corrections.

Hypotheses and clauses, matched individually:

- Extension of algebraically closed fields: `(k k' : Type u)` with `[Field k]`,
  `[IsAlgClosed k]`, `[Field k']`, `[IsAlgClosed k']`, `[Algebra k k']`.
  The algebra map between fields is injective. A common universe permits any pair of
  fields after universe enlargement and matches the scheme-category pullback API.
- Smooth proper connected curve X/k: `(X : Scheme.{u})`,
  `(s : X ⟶ Spec (.of k))`, `[IsConnectedCurve s]`, `[Smooth s]`, `[IsProper s]`.
  The recorded IsConnectedCurve includes separatedness, finite type, nonemptiness,
  connectedness and dimension exactly one.
- Rational closed point P: `(P : X)` and `(hP : P ∈ closedPoints X)`.
  Every closed point of a finite-type scheme over algebraically closed k has residue
  field k, so this is exactly the requested rational closed-point restriction;
  it does not require an arbitrary, possibly incompatible residue-field identification.
- X' and its projection: `pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k')))`
  and `pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k k')))`, using the
  dependency's base-change convention. They are fully explicit throughout the statement.
- Unique point P' over P: the existential `P'`, the first-projection equality with P,
  and the universal clause saying every Q with that same image equals P'.
- Both local rings are DVRs: the two `IsDiscreteValuationRing` conjuncts at P and P'.
- Rational pullback: the existential ring homomorphism `ρ : X.functionField →+*
  X'.functionField` is constrained on the entire original stalk at the image of P'
  by the scheme projection's `stalkMap`. Each original stalk has X.functionField
  as fraction field; hence this specifies the canonical map uniquely, rather than
  allowing an unconstrained function-field map. The image-point formulation avoids
  a cast along the already stated equality of that image with P.
- Every nonzero f and its nonzero pullback: `∀ f : X.functionFieldˣ` and `ρ f`.
  Ring homomorphisms of fields are injective, so the pulled-back element is nonzero.
- Equality of normalized orders: `X'.ord (ρ f) P' = X.ord (f : X.functionField) P`.
  This is the exact order used by the recorded principal-divisor declaration.

Four existential class witnesses (integrality and local Noetherianity for X and X')
precede the function-field and order clauses to make these APIs well typed. These
are derived structures, asserted in the conclusion, not additional hypotheses.
Smooth connected curves are integral and finite-type schemes over fields are
Noetherian; these properties also hold after the specified field extension.
Ordinary existential class binders register their witnesses for instance synthesis,
so no `let`, file-local instance, or private definition is used.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsCurve` and
  `AlgebraicGeometry.IsConnectedCurve`, including their complete signatures/docstrings.
- `def-sc-field-extension` is a bundle: its record explicitly prescribes
  `Spec.map (CommRingCat.ofHom (algebraMap k k'))`, `Limits.pullback`, and
  `pullback.fst`. Its principal declaration `AlgebraicGeometry.Etale.cohomologyMap`
  in `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance` was read;
  cohomology/sheaf inverse image is not needed for this local-ring node.
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`: the recorded use of
  `CategoryTheory.Limits.pullback` / `pullback.fst` for scheme base change.
- `Sheaf.AlgebraicGeometry.DivisorModule`: the bundle's principal-divisor clause
  reuses `AlgebraicGeometry.Scheme.div` from
  `WeilConjectures.AlgebraicGeometry.Curve.Divisor`, whose docstring and definition
  use `AlgebraicGeometry.Scheme.ord` from `Mathlib.AlgebraicGeometry.OrderOfVanishing`.
  The full ord definition was read; at a codimension-one point it is the integer
  order from Ring.ordFrac. These closed curve points are exactly codimension one.
- Mathlib's `Scheme.functionField`, `stalkFunctionFieldAlgebra`, and
  `Scheme.Hom.stalkMap` supply the function fields, injections and compatibility.

Edge cases checked: the identity extension; transcendental extensions of arbitrary
size in a common enlarged universe; arbitrary characteristic including positive
characteristic; f = 1, a uniformizer, its inverse and products (orders 0, 1, -1 and
additive); the zero function is excluded by the units type; empty and dimension-zero
schemes are excluded precisely by IsConnectedCurve, as the node requests; the generic
point is not closed in dimension one and is consequently not inadvertently included.
The rationality restriction matters: points with larger residue fields can have
multiple points over them after extension. Here algebraic closedness and finite type
force residue field k, so the fibre is Spec k' and has exactly one point.

Searches performed:

- msearch.py leanfinder: "order of vanishing at a rational point of a smooth curve
  is unchanged by extension of algebraically closed fields". Eight results, all
  WeierstrassCurve point maps, slopes, minimal models or elliptic function fields;
  none gives the scheme-level statement.
- msearch.py loogle: `Ring.ordFrac_eq_ord`. One result in
  Mathlib.RingTheory.OrderOfVanishing.Basic comparing a stalk element to its image
  in its own fraction field, not orders under scalar extension.
- msearch.py grep: `ordFrac.*baseChange|baseChange.*ordFrac|ord.*pullback`, in
  Mathlib/AlgebraicGeometry: zero hits.
- msearch.py leansearch: "order of vanishing at rational point preserved under
  field extension". Service unavailable (Internal Server Error), recorded as such.
- rg over WeilConjectures and lean/Sheaf for function-field map/pullback names:
  no existing general rational-pullback/order-preservation statement. Read the
  available FunctionField, Curve/Divisor and Curve/Affine APIs.
- rg for the item id in WeilConjectures: zero hits; rg for
  `local_dvr_base_change|ord.*baseChange|baseChange.*ord` in the project: zero hits;
  proposed full declaration name absent from dag/lean_names_upstream.json, Mathlib,
  WeilConjectures and lean/Sheaf before this delivery.

The theorem docstring carries all three node proof steps, with their named inputs.
No mathematical fault or STATEMENT-DISPUTED issue found. The server compiled the
80-line module cleanly in 2.2 seconds, with no warnings. The delivery dry run printed OK (commit df80b755b): server compilation and
preflight passed, with only the independent second reading left to its assigned reader.
Nothing was pushed.

Source checked: the original blueprint file was read from the project server
(the local literature copy is absent). Its affine-case unit quotient paragraph
uses the same rational deleted set and its boundary divisor after scalar extension.
The present node supplies precisely the preservation of its local coefficients.

## Second reading by M1

Independently opened the node, its delivered Lean file, all four statement-dependency
nodes and the declarations below. No mathematical or signature mismatch found; the
Lean and node record are retained verbatim. This delivery has no new definition nodes,
no dependency modules and no statement correction requiring citer review.

Object/hypothesis/conclusion checklist (each verdict: matches):

- Objects k and k', an extension of algebraically closed fields: `(k k' : Type u)`
  with both `Field` and `IsAlgClosed` instances and `[Algebra k k']`. A unital field
  map is injective, so this renders the inclusion without imposing algebraicity,
  finite degree or a characteristic restriction.
- Object X, smooth proper connected curve over k: `(X : Scheme.{u})`, structure
  morphism `s : X ⟶ Spec (.of k)`, `[IsConnectedCurve s] [Smooth s] [IsProper s]`.
  Opened Curve.lean: IsConnectedCurve extends IsCurve (separated, locally finite
  type, quasi-compact, dimension at most one), adds ConnectedSpace and dimension
  exactly one. Thus all the curve hypotheses, including nonemptiness, match.
- Object P, rational closed point: `(P : X) (hP : P ∈ closedPoints X)`. Over an
  algebraically closed field, every closed point of a finite-type k-scheme has
  residue field k as a k-algebra. The rationality condition is therefore equivalent
  here, and no independent choice of a residue-field isomorphism is needed.
- Object X' and projection: every occurrence is the same `pullback s
  (Spec.map (CommRingCat.ofHom (algebraMap k k')))` and `pullback.fst`.
  Opened BaseChangeConventions.lean and its node: these are explicitly the recorded
  scheme base change and projection to X. The field-extension dependency's bundle
  note uses exactly this map; its cohomologyMap declaration (opened in
  TopologicalInvariance.lean) concerns the other, unused sheaf/cohomology clauses.
- Object P', uniquely over P: `∃ P'`, the `pullback.fst ... P' = P` conjunct and
  `∀ Q, pullback.fst ... Q = P → Q = P'`. Uniqueness is global in X', not limited
  to an affine chart. The node's unique-point notation is fully justified.
- First conclusion, both local rings DVRs: `IsDiscreteValuationRing
  (X.presheaf.stalk P)` and the corresponding stalk of the actual pullback at P'.
  Neither ring is replaced by a chosen abstract isomorphic DVR.
- Objects k(X), k(X') and the rational pullback f': the existential ring hom `ρ`
  is compatible, on every element r of the source stalk at the image of P', with
  the projection's `stalkMap P'`. Opened Mathlib FunctionField.lean: the algebraMap
  is stalk specialization to the generic point and both stalks have the displayed
  function fields as fraction rings. Opened Scheme.lean: stalkMap has precisely
  source stalk at the image and target stalk at P'. The compatibility determines
  the extension to fractions uniquely, so ρ is the canonical pullback, not an
  unconstrained field embedding. The point-image equality transports the source
  stalk to the named P without introducing a hidden let or cast assumption.
- Quantifier, every nonzero rational f: `∀ f : X.functionFieldˣ`. In a field,
  units are exactly nonzero elements. Its pullback `ρ f` is automatically nonzero
  because a ring hom between these fields is injective.
- Final conclusion, equal normalized orders: `X'.ord (ρ f) P' = X.ord
  (f : X.functionField) P`. Opened the divisor dependency and DivisorModule.lean,
  Curve/Divisor.lean (`Scheme.div`, `div_apply`) and Mathlib OrderOfVanishing.lean
  (`ord`, `ordHom`): div uses exactly ord, which at codimension one is Ring.ordFrac
  converted to the integer exponent. DVR stalks have dimension one, so the junk
  value away from codimension one cannot weaken this conclusion.
- The four existential witnesses `IsIntegral X`, `IsIntegral X'`,
  `IsLocallyNoetherian X`, `IsLocallyNoetherian X'` supply API structures in the
  conclusion, adding no input hypothesis. Smooth connected curves over an
  algebraically closed field are integral; their base changes are again smooth
  connected curves. Finite type over either field gives Noetherianity. These
  witnesses express automatic properties, not an additional substantive clause.

Source reading: retrieved the named blueprint thm-sc-constant-invariance from the
project server. Its affine-case unit quotient argument uses the smooth proper
compactification and the same rational boundary points after base change. The
prime-to-characteristic integer n belongs to the cohomology argument; neither the
local valuation comparison nor this node mentions n. Also read the Stacks algebra.tex
source at tags 00E6 (remark-fundamental-diagram) and 00PD (lemma-characterize-dvr),
resolving the tags using tags/tags. The first applies to arbitrary ring maps and
primes; the second characterizes DVRs and derives the unit-times-uniformizer exponent
and fraction-field valuation. No omitted standing hypotheses found. The theorem
proof docstring follows all three node steps with their cited nodes and source place.

Edge cases: identity and transcendental extensions are included; both positive and
zero characteristic are included. Empty and zero-dimensional schemes are excluded
by the node's connected-curve definition, not by a new assumption. P is closed,
so the generic point of the integral dimension-one curve is excluded as intended.
f = 0 is excluded by the node and units binder alike; f = 1, uniformizers, inverses
and products correspond to exponents 0, 1, -1 and addition. There is no index set
or n in this statement. The shared universe u can be chosen to contain both fields
and the scheme; it imposes no small-test-object quantifier or bound on extension
cardinality. All variables and the universe are explicitly bound.

Independent searches:

- LeanFinder via msearch: `scheme stalk discrete valuation normalized valuation
  invariant scalar extension`. Eight ingredient hits: ValuativeCommSq fields and
  valuation rings, stalkFunctionFieldAlgebra and IsFractionRing; no exact theorem.
- Loogle via msearch: `IsDiscreteValuationRing, Algebra.TensorProduct` did not
  resolve Algebra.TensorProduct. Retried `IsDiscreteValuationRing, Ring.ordFrac`:
  eight hits about uniformizers and valuation descriptions in a single DVR,
  including ordFrac_irreducible and ordFrac_eq_valuation_inv, no scheme base change.
- LeanSearch via msearch: `rational function order unchanged extending algebraically
  closed base field`; service unavailable (Internal Server Error), no verdict inferred.
- rg on Mathlib algebraic geometry/ring theory, WeilConjectures and project Sheaf:
  `ord.*(extension|tensor|scalar)|valuation.*base.change|base.change.*valuation`.
  Opened the useful hit Ring.ordOf_map in upstream OrderOfVanishing/Noetherian.lean:
  it assumes both DVRs and equality of extended maximal ideals; it neither constructs
  the base-changed curve nor proves its stalk is a DVR or the fibre point is unique.
  Also opened the landed dvr_field_extension_order module: it is an algebraic
  tensor/localization statement, a proof ingredient, not this scheme statement.
  No exact existing declaration found. Proposed name absent from upstream name map.

No hollow definitions, private notions, file-local notation/instances, let binders,
extra proofs or unused convention imports occur. The only proof is the named theorem's
`by sorry`. The recorded lean.statement was checked for literal equality to the
entire file signature. Second reading changed only this report; compilation and
preflight results are recorded below.

Validation: independent scompile succeeded in 4.2 s, exit 0, no warnings.
Delivery dry run printed OK: server compilation and stage-2 preflight passed.
