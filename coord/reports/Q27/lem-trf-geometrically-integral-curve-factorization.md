# Q27: geometrically integral curve factorization — stage-2 repair

## Worker report

H1 is repaired by the new module
`lean/Sheaf/AlgebraicGeometry/GeometricallyIntegralCurveFactorization.lean`, declaring
`AlgebraicGeometry.exists_geometricallyIntegralCurveFactorization`. Its sole proof is
`by sorry`; there is no new definition or hidden existence choice. The module and theorem
have source and blueprint docstrings. The theorem docstring includes every one of the
current node's thirteen proof steps and each step's dependency ids.

H2 is repaired by taking the current main node as the base and adding only `lean`.
In particular `blueprint.from.place`, `split_report`, `statement`, `stmt_deps`, `proof`
and `proof_deps` are unchanged. The stale stage-1 head is not reused. The two requested
dependency node copies likewise differ only in `lean`; their existing `mathlib_match`
records and statuses remain unchanged. No unit or target statement is changed.

I read the actual source, de Jong, *Families of curves and alterations* (1997), Lemma 5.2
and its proof, printed pp. 612–613, in the publisher's PDF:
https://www.numdam.org/item/10.5802/aif.1575.pdf . Its graph modification, normal model
and Stein factorization are the source of the node. The item keeps the trivial group
and properness conclusions. The complementary dimension follows from the transcendence-degree tower formula;
the finite-total-dimension clause is the node's Stacks 02JX consequence.

The statement is rendered hypothesis by hypothesis and clause by clause as follows.

| Node clause | Lean rendering |
| --- | --- |
| Schemes X and S | `{S X : Scheme.{u}}`, with explicit `universe u` |
| X and S integral | `[IsIntegral S] [IsIntegral X]` |
| X and S excellent | `hS` and `hX`, namely `∀ U, IsAffineOpen U → IsExcellent Γ(_, U)` |
| X and S Noetherian | `[IsLocallyNoetherian S] [CompactSpace S]` and the same pair for X; these are exactly the two fields of Mathlib `IsNoetherian` |
| A proper dominant f : X → S | `(f : X ⟶ S) [IsProper f] [IsDominant f]` |
| The generic point of S | `(ηS : S) (hηS : IsGenericPoint ηS Set.univ)`; integral schemes are sober irreducible and have exactly one such point, so this only names the point |
| Generic fibre geometrically integral | `hgeom : GeometricallyIntegral (f.fiberToSpecResidueField ηS)` |
| Generic fibre dimension d ≥ 2 | `(d : ℕ) (hd : 2 ≤ d)` and `hdim : topologicalKrullDim (f.fiber ηS) = (d : WithBot ℕ∞)` |
| There exist X′ and Y | `∃ (X' Y : Scheme.{u})` |
| X′ and Y integral | `IsIntegral X' ∧ IsIntegral Y` |
| X′ and Y excellent | The two quantified all-affine `IsExcellent Γ(_, U)` conjuncts |
| X′ and Y Noetherian | `IsLocallyNoetherian X' ∧ CompactSpace X' ∧ IsLocallyNoetherian Y ∧ CompactSpace Y` |
| π : X′ → X a proper birational modification | `(π : X' ⟶ X)`, `IsProper π`, and `∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (π ∣_ U)`; the restriction has domain the entire inverse image of U |
| Proper dominant g and h | `(g : X' ⟶ Y) (h : Y ⟶ S)` with `IsProper g ∧ IsDominant g ∧ IsProper h ∧ IsDominant h` |
| Factorization fπ = hg | `π ≫ f = g ≫ h` |
| Generic point of Y | Existential `ηY : Y` and `IsGenericPoint ηY Set.univ`; this names the unique generic point of integral Y |
| Generic fibre of g geometrically integral, dimension 1 | `GeometricallyIntegral (g.fiberToSpecResidueField ηY)` and `topologicalKrullDim (g.fiber ηY) = (1 : WithBot ℕ∞)` |
| Generic fibre of h geometrically integral, dimension d−1 | `GeometricallyIntegral (h.fiberToSpecResidueField ηS)` and `topologicalKrullDim (h.fiber ηS) = ((d - 1 : ℕ) : WithBot ℕ∞)` |
| If S and X have finite dimension, so do Y and X′ | `(topologicalKrullDim S < ⊤ ∧ topologicalKrullDim X < ⊤ → topologicalKrullDim Y < ⊤ ∧ topologicalKrullDim X' < ⊤)`; in `WithBot ℕ∞`, strictly below top is exactly finite dimension |

The instance and ordinary binders are all explicit. The generic-fibre assumptions concern
only the indicated fibre, not all fibres of f; there is no flatness, smoothness,
projectivity, perfectness, characteristic, finite-total-dimension or field-base assumption.
Naming `ηS` and existential `ηY` adds no geometric condition: `genericPoint_spec` supplies
such a point for every integral scheme, and `IsGenericPoint.eq` gives uniqueness.

Statement dependency declarations, whose signatures and documentation were opened:

| Dependency | Module and declaration used |
| --- | --- |
| `def-weil-proper-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper` |
| `def-pc-integral-scheme` | `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral` |
| `def-exc-excellent-ring` | `Sheaf.RingTheory.ExcellentRing`, `IsExcellent` |
| `pqf-def-locnoeth` | `Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsLocallyNoetherian` |
| `def-weil-pbc-quasi-compact-scheme` | `Mathlib.Topology.Defs.Filter`, `CompactSpace` |
| `def-pc-scheme-fibre` | `Mathlib.AlgebraicGeometry.Fiber`, `Scheme.Hom.fiber` and `Scheme.Hom.fiberToSpecResidueField` |
| `def-pc-geometrically-irreducible` | `Mathlib.AlgebraicGeometry.Geometrically.Integral`, `AlgebraicGeometry.GeometricallyIntegral`; the node's other three notions are the existing classes in `Irreducible`, `Reduced` and `Connected` |
| `def-kun-topological-krull-dimension` | `Mathlib.Topology.KrullDimension`, `topologicalKrullDim` |
| `def-sc-generic-point` | `Mathlib.Topology.Sober`, `IsGenericPoint`, with `genericPoint`/`genericPoint_spec` giving existence |

The `GeometricallyIntegral` class is `geometrically IsIntegral`. Over `Spec k`,
`geometrically_iff_of_commRing` quantifies over every field extension. Thus the fibre
clauses use precisely the scheme-theoretic base change required by the node.
The four geometric-property class docstrings and `geometrically` were read; no new
geometric-integrality predicate is introduced. Excellence uses the recorded ring
predicate, not an independently defined excellence class.

All recorded modules of stated proof dependencies are imported without `public` unless
already needed by the statement. The Mathlib-leaf proof modules are also imported.
The currently unstated proof nodes `lem-trf-excellent-scheme-affine-cover`,
`lem-trf-geometric-reducedness-separable-scalar-restriction`, `lem-zl-finite-separable-closure`
and `lem-trf-closed-dominant-dimension` have no recorded module to import; they remain
proof-plan steps, not extra hypotheses or fabricated theorems.

Edge cases checked against the source and signature: d = 2 gives two one-dimensional
generic fibres and avoids natural-number subtraction ambiguity. d = 0 and d = 1 are
excluded exactly by `2 ≤ d`. Empty X or S are excluded exactly by integrality; a dense
open U in integral X is nonempty. A field-spectrum base, imperfect positive-characteristic
base, already-normal X and degree-one Stein constants are allowed. Infinite-dimensional
Noetherian schemes are allowed, since the finite-dimension statement is an implication
inside the conclusion. A dense-open isomorphism is stronger than being merely finite
over that open, and is the exact modification convention in this node.

Searches for an existing full statement were made before writing. The prescribed
`msearch.py` tool returned:

- `grep` query `curveFactor|CurveFactor|Stein|stein`: 0 hits; [].
- `loogle` query `AlgebraicGeometry.GeometricallyIntegral, AlgebraicGeometry.IsProper, IsGenericPoint`: 0 hits; [].
- `leanfinder` query `A proper dominant morphism of integral excellent Noetherian schemes with geometrically integral generic fibre factors after a proper birational modification through a geometrically integral generic curve`: 8 hits; ['AlgebraicGeometry.Scheme.Hom.instIsDominantToNormalization', 'AlgebraicGeometry.IsIntegralHom', 'AlgebraicGeometry.finite_appTop_of_universallyClosed', 'AlgebraicGeometry.IsIntegralHom.instUniversallyClosed', 'AlgebraicGeometry.Scheme.Hom.instIsIntegralNormalization', 'AlgebraicGeometry.Scheme.Hom.instIsIntegralHomNormalizationDesc', 'AlgebraicGeometry.Scheme.Hom.toNormalization', 'AlgebraicGeometry.Scheme.Hom.normalizationDesc'].
- `leansearch` query `proper birational modification factorization geometrically integral generic curve excellent Noetherian schemes`: 8 hits; ['AlgebraicGeometry.IsProper.mk', 'AlgebraicGeometry.isProper_iff', 'AlgebraicGeometry.IsProper', 'AlgebraicGeometry.IsProper.toLocallyOfFiniteType', 'AlgebraicGeometry.isProper_eq', 'AlgebraicGeometry.IsIntegralHom.hasAffineProperty', 'AlgebraicGeometry.IsProper.toIsSeparated', 'AlgebraicGeometry.IsProper.instOfIsFinite'].

The LeanFinder results were normalization and properness lemmas, not this factorization;
Loogle and Mathlib grep found no exact statement; LeanSearch returned the properness
class and basic permanence lemmas. Direct `rg` of both `WeilConjectures/` and `lean/Sheaf`
for `geometrically.integral.*[Ff]actor|curveFactor|CurveFactor|Stein|stein` found the older
field/trait relative-curve statement, the downstream de Jong tower, and affine Stein
factorization tools. I opened `RelativeCurveFactorization.lean`: it allows only a field
or trait base and controls transcendence degree rather than both geometrically integral
generic fibres, so it cannot be reused. I also searched for the item's blueprint id;
there is no upstream theorem with this complete statement. The proposed declaration name
has no existing match in either project or Mathlib. No statement dispute or correction
was needed.

Validation: the full delivered theorem module passed the prescribed single-file
`scompile.py` compile with no errors and no warnings. The delivery dry run additionally
checks the existing dependency declarations and every delivered Lean file. The final
dry-run result is recorded below after running it.

## Dependency modules

`def-pc-geometrically-irreducible`: section 1(B) lean-only repair requested by the return.
Its `mathlib_match` already gives exactly the four notions, but no `lean` record existed.
The new existing-Mathlib record names `GeometricallyIntegral` from
`Mathlib.AlgebraicGeometry.Geometrically.Integral`, the class used by this consumer,
and lists the reduced and irreducible classes imported by that module. The connected
class is in `Mathlib.AlgebraicGeometry.Geometrically.Connected`, explicitly imported by
the theorem module. Both the record note and the unchanged `mathlib_match` explain
all four specializations over a field. No replacement definition module is appropriate,
since it would duplicate Mathlib. All non-lean fields remain identical to the base.

`def-sc-generic-point`: section 1(B) lean-only repair requested by the return.
Its `mathlib_match` is exact, but had no `lean` record. The existing-Mathlib record names
`IsGenericPoint` and lists `genericPoint` and `genericPoint_spec`, all in
`Mathlib.Topology.Sober`. `closure {x} = Z` includes x ∈ Z, closedness and irreducibility;
for a scheme component this is exactly the node. The consumer uses `IsGenericPoint`
on the whole integral scheme, and a canonical point is supplied by `genericPoint` if
needed. No second generic-point definition or narrowed specialization is introduced.
All non-lean fields remain identical to the base.

## Second reading by Q27

The dispatcher requires direct delivery and forbids starting another agent. This is
a separate final cross-check by the same worker; the maintainer supplies the independent
review, as the current direct-delivery workflow specifies.

With the current DAG node and complete Lean signature open, I checked each row of the
hypothesis/conclusion table again. Integral/excellent/Noetherian occurs for all four
schemes. Properness and dominance occur for f, g and h. The modification condition
uses `IsIso` on the full inverse image of a dense open, not `IsFinite`. The commuting
square has the order `π ≫ f = g ≫ h`. The input geometric-integrality assumption is
on `f.fiberToSpecResidueField ηS`; the output ones are on g over ηY and h over ηS.
Their dimensions are respectively d, 1 and d−1. Total dimensions are conditional
on both S and X being finite-dimensional and bound both Y and X′. There is no group
action or projectivity in the signature. The named generic points introduce no new
geometric assumption, and are uniquely determined for these integral schemes.

I reopened the dependency records and Mathlib definitions. During this check I corrected
the geometric-properties record's primary module from `Irreducible` to `Integral`,
so the recorded module actually exposes the class used by the consumer and every
name listed in `lean.declarations`. The connected class's separate module is documented
and explicitly imported. The generic-point record exposes all three listed declarations.
I compared all three sandbox JSON files to the current base after removing `lean`:
they agree exactly, including `blueprint.from.place` and `split_report`. The statement
record is extracted verbatim from the theorem's keyword through its signature. The
proof is only `sorry`, the thirteen source/proof steps are documented, every variable
and universe is bound explicitly, and every Lean line is at most 100 characters.
No mathematical mismatch or statement correction remains.

## Delivery validation

`deliver2.py Q27 lem-trf-geometrically-integral-curve-factorization --no-push` returned
`OK (dry run): commit 06d78b2585 passes the preflight and compiles; nothing pushed`.
It checked the theorem module and the existing-declaration probes, with no errors or
non-sorry warnings. The delivery contains exactly the theorem module, the three node
lean records and this report. The final delivery wrapper repeats these checks before pushing.
