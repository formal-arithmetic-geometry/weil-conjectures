## Worker report

The delivery states `AlgebraicGeometry.exists_admissible_quotient_affine_integral_charts`
in `Sheaf.AlgebraicGeometry.AdmissibleQuotientAffineIntegralCharts`. It introduces no
new definitions, nodes, dependency replacements, or statement changes. Its sole theorem
has proof `sorry`; its docstring gives all eleven proof steps and the dependency ids.
The copied node differs from the current shared node only in `lean`.

The previous worker's stale-dispatch diagnosis concerned Q145's **stage-1 split**,
merged at 2026-10-18T23:04:21Z. The present node has `status: split`, an eleven-step
proof and no `lean` record. This is the next, stage-2 task, not another split or a
re-push of Q145's delivery. Q145's mathematical statement, proof and review are retained.

I read the entire node, every statement dependency and its recorded interface, the
stage-2 brief, stage document and delivery-errors H, and the compact-object example.
I read ILO IX 1.4 at printed pp.132--133 (text extracted from the supplied PDF) and
Stacks `groupoids.tex`, `lemma-integral-over-invariants` (03BJ) and `lemma-points`
(03BL). ILO uses the admissible quotients in (*); the DAG supplies the explicit
eleven-step construction, rather than claiming ILO proves the general theorem.

The node's hypotheses and conclusions match the signature as follows:

- Scheme: `(M : Scheme.{u})`; finite group: `(H : Type v) [Group H] [Finite H]`;
  action by scheme automorphisms: `(a : H →* Aut M)`. There is no base scheme,
  separatedness, finite type, Noetherianity, tameness or invertible-order assumption.
- Admissibility: `_hadmissible` says that for every `x`, there is an affine open `W`
  containing `(a h).hom x` for every `h`. This is the whole point orbit, not merely
  an affine neighbourhood of the individual point.
- Quotient existence: `∃ (Q : Scheme.{u}) (q : M ⟶ Q)`. The first conjunct says
  `(a h).hom ≫ q = q` for every group element. The next conjunct quantifies over
  all schemes `Z` and invariant maps `f : M ⟶ Z` and gives `∃! g, q ≫ g = f`.
  The target need not be affine or separated.
- Affine, integral and surjective: `IsAffineHom q ∧ IsIntegralHom q ∧ Surjective q`.
  In particular this does not use `IsFinite q`.
- Orbit-space topology: `Topology.IsQuotientMap q` together with
  `q x = q y ↔ ∃ h, (a h).hom x = y`. Thus the fibres are exactly orbits and the
  topology is the quotient topology on those fibres, with no extra topology chosen.
- Geometric orbit fibres: for every algebraically closed field `Ω : Type u`, the
  postcomposition map from `Spec (.of Ω) ⟶ M` to `Spec (.of Ω) ⟶ Q` is surjective,
  and two such points have the same image iff `t ≫ (a h).hom = s` for some `h`.
  This spells out the geometric-point assertion of 03BL, including surjectivity.
- Stable affine covering: `∀ x, ∃ V _hV hW, ...`, with
  `_hV : IsAffineOpen V`, `hW : IsAffineOpen (q ⁻¹ᵁ V)` and `x ∈ q ⁻¹ᵁ V`.
  Here `W` is written directly as `q ⁻¹ᵁ V`, so `q⁻¹(q(W)) = W` follows from
  the explicitly required `q '' (q ⁻¹ᵁ V : Set M) = (V : Set Q)`.
  The displayed equivalence for every `h,y` explicitly says that W is H-stable.
  This existential affine family is a covering because it contains every x.
- Canonical invariant-ring charts: `C : Subring Γ(M, q ⁻¹ᵁ V)` has an exact
  membership equivalence specifying all the fixed sections; it is not an
  unconstrained ring or an assumed quotient object. With `B = Γ(M, W)`, `hW.isoSpec`
  is the canonical `W ≅ Spec B`. The existential `e : V.toScheme ≅ Spec (.of C)`
  is constrained by
  `hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom C.subtype) = (q ∣_ V) ≫ e.hom`.
  Hence the actual restricted q is Spec of the inclusion of the actual fixed
  subring. This also determines e uniquely, since the restricted q is surjective
  and its section map is injective by the other clauses; no arbitrary map or
  chosen Nonempty quotient replaces the canonical construction.
- Every affine open: `∀ V, IsAffineOpen V → IsAffineOpen (q ⁻¹ᵁ V) ∧ ...`.
  `Function.Injective (q.app V).hom` and the exact image criterion for every s
  identify `Γ(Q,V)` with the invariant subring of `Γ(M,q ⁻¹ᵁ V)` under the
  canonical section map, not merely by an abstract ring isomorphism.
- Restriction to every invariant open: for `U` with `_hU` expressing H-stability,
  the last clause produces an open V with `q '' U = V` and `q ⁻¹ᵁ V = U`.
  For every scheme Z and invariant `f : U.toScheme ⟶ Z` it supplies a unique
  `g : V.toScheme ⟶ Z` with `q.resLE V U hUV ≫ g = f`. The proof binder `hUV`
  is just the inclusion needed to form the canonical restricted morphism.
  U need not be affine or quasi-compact, and may be empty or all of M.

In both section-invariance conditions, the pullback and restriction are compared
on every common subopen D using the actual maps `appLE` and `presheaf.map`.
For a stable W this is equivalent to the usual fixed-section condition: one may
take D = W, since W is contained in every inverse image of W. Conversely, equality
on W restricts to equality on every D by functoriality. This avoids equality casts
between isomorphic open-subscheme presentations. For the open restriction's
invariant morphism f, the analogous comparison is
`(a h).hom.resLE U D hDh ≫ f = M.homOfLE hD ≫ f`.
On stable U the case D = U gives precisely invariance under its restricted action;
all other D are restrictions of that equation. It is not merely pointwise invariance.

Statement dependency declarations used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`. Their full signatures and docstrings were
  read in that file; Hom is the locally ringed-space morphism structure.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map` in the same
  module. The latter applies contravariantly to the inclusion C -> B.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsIntegralHom`, defined
  in `Mathlib.AlgebraicGeometry.Morphisms.Integral`, is the integral half of the
  node's recorded declarations; the record names both it and `IsFinite`, whose
  owner is `Mathlib.AlgebraicGeometry.Morphisms.Finite`. Both modules are imported.
  The integral definition is affine plus integral section maps for every affine
  target open, exactly the node's notion. Both class signatures/docstrings read.
- `def-weil-surjective-morphism`: `AlgebraicGeometry.Surjective` in
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`; its single field is
  `Function.Surjective f`, read directly in that file.

Every available proof-dependency owner is imported privately, including
`Sheaf.AlgebraicGeometry.AffineGroupoidOrbitFibres`,
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Affine`, and the Mathlib owners
for prime avoidance, the prime-spectrum topology, finite coproducts, affine basic
opens/intersections, etale coproducts and locally ringed-space morphisms. Some are
already reachable from other imports but are recorded explicitly for stage 3.
The source of the upstream affineness criterion was obtained with
`scompile.py --source WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Affine`
because it is absent in the older local upstream checkout. No proof import is
omitted for a cycle.

Edge cases checked:

- M empty: choose the empty scheme, with vacuous point/chart cover conditions;
  section maps on empty opens are the identity of the zero ring. The categorical
  property includes the unique map out of the empty scheme.
- The trivial group gives the identity quotient and all sections fixed.
- Characteristic dividing |H| and nonreduced M are allowed. The statement and the
  proof use no averaging or division by |H| and do not claim reduced fibres.
- Nonseparated M (for example the doubled-origin affine line) is not excluded;
  Step 1 uses separated intersections inside the ambient affine U only.
- Arbitrary invariant opens, including empty/top and non-quasi-compact opens,
  are in the last universal quantifier.
- The invariant localization argument allows zero divisors and f = 0.
- Integral does not mean finite: in characteristic different from 2, take the
  square-zero ring k plus an infinite-dimensional k-vector space V and let C2
  negate V. Its invariant ring is k; the inclusion is integral but not a finite
  module extension. The theorem imposes no module-finiteness conclusion.
- H has an independent universe v. Schemes, target schemes and algebraically
  closed test fields use the common scheme universe u; no finite/small index
  restriction or additional universe equality is imposed on H.

Searches made with the prescribed wrapper (outputs retained in searches.jsonl):

- LeanFinder: `An admissible finite group action on a scheme has an affine integral
  categorical quotient with invariant affine charts`. Eight hits: generic affine
  morphism criteria, finite morphisms, integral affine-space maps and finite-set
  Galois quotients; no theorem asserting this quotient construction.
- Loogle: `IsIntegralHom, Scheme, quotient`. Zero hits; the service reports
  `unknown identifier 'IsIntegralHom'`, so this query gives no positive match.
- Mathlib grep: `admissible|invariant.*quotient|quotient.*invariant`, in
  `Mathlib/AlgebraicGeometry`. Zero hits.
- LeanSearch: `An admissible action of a finite group on a scheme has an affine
  integral categorical quotient with invariant affine charts and geometric orbit
  fibres`. Eight hits, all generic group actions, orbit sets and topology; no
  scheme-quotient construction.
- Direct rg in the upstream `WeilConjectures` and project's `lean/Sheaf`:
  `admissible_quotient|admissibleQuotient|AdmissibleQuotient|admissible.*quotient|quotient.*admissible`.
  No upstream theorem for this item. Side hits are uses in other proof docstrings
  and the finite-quotient definition `IsAdmissibleFiniteSchemeQuotient`. I read
  that definition; it requires `IsFinite π` and therefore cannot encode this
  arbitrary integral quotient. It has not been duplicated or weakened here.
- Direct search for the item id in upstream WeilConjectures found no declaration.
  `exists_admissible_quotient_affine_integral_charts` is absent in the upstream
  name index, upstream sources, Mathlib and side library (name collision check).
- Read upstream finite-etale Galois quotients and the side
  `freeFiniteGroup_affine_quotient`: those have finite-etale or affine-over-a-base
  and free-action hypotheses, respectively, and do not state this node.

No STATEMENT-DISPUTED issue or node fault was found. No existing finite quotient
predicate is used in place of the node's integral quotient. All variables and both
universes are explicitly bound; there are no local notations, local instances,
helper theorems, hollow definitions, or data choices from postponed theorems.

Validation: the prescribed scompile.py compiled the module both as a sandbox file
and under its actual library name, cleanly (2.1 s and 2.2 s). The initial run exposed
only a missing public import of IsAlgClosed and an ambiguous `.ofHom` notation;
those were repaired with the exact public import and `CommRingCat.ofHom`.
The final dependency-import-only adjustment and delivery preflight are checked below.

## Second reading by Q115

This is the dispatch worker's second, separate pass over the complete node and the
complete final signature; no other agent was started, as explicitly instructed.
The maintainer's independent review remains the independent reading of the delivery.

I checked all four input objects/conditions against the node: M is any scheme,
H is finite, a is an action by automorphisms, and every entire orbit has an affine
neighbourhood. I checked the quotient invariance and unique factorization first,
then all three map properties, the quotient topology and ordinary orbit relation,
and both assertions about algebraically closed-field points. I checked the
chart's canonical equation against the source/codomain of `hW.isoSpec.hom`,
`Spec.map (CommRingCat.ofHom C.subtype)` and `q ∣_ V`: both sides map W to Spec C.
The exact subring membership condition makes C equal to B^H. Because W is the
inverse image of V and its image is V, the required saturation equality is present,
not assumed of an arbitrary stable affine. The chart family covers M pointwise.
I separately checked the section assertion for every affine V, rather than only
for the chosen chart family. Finally I checked that the universal property on
arbitrary invariant U is for scheme morphisms, via resLE on all common subopens,
not merely for underlying maps of points.

The initial import and constructor defects described above were fixed. No
mathematical mismatch was found in this pass; there is no statement correction,
missing condition, finite-module requirement, freeness or order-invertibility
assumption. The proof docstring preserves all eleven DAG steps. The node record
copies the multiline signature verbatim, and leaves every previous field intact.

Final validation: after the last explicit dependency import, scompile.py passed
again under both names (3.0 s sandbox, 2.9 s library), without errors or warnings.
The prescribed `deliver2.py Q115 lem-per-admissible-quotient-affine-integral-charts
--no-push` printed `OK (dry run): commit 2bc2a035d7 passes the preflight and compiles;
nothing pushed`. A direct read-only comparison also confirmed all non-lean node
fields unchanged, the signature copied verbatim, exactly one sorry, and no Lean
line over 100 characters. The final delivery reruns its own preflight and compile.
