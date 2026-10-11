## Worker report

The module states `AlgebraicGeometry.product_tangentSpace_directSum` in
`Sheaf.AlgebraicGeometry.ProductTangentSpaceDirectSum`. It imports the existing
`tangent-space` definitions from `Sheaf.AlgebraicGeometry.SchemeTangentSpace`.
The theorem has a field `k`, schemes and structure maps, a product object with
projections and point inclusions, the projection and inclusion identities, and
maps `dX`, `dY`, `jX`, `jY` rendering the differentials. Its conclusion is an
additive isomorphism from the product tangent space to `TX × TY`; the first
conjunct identifies its two components with the projection maps and the last
two conjuncts identify the inverse on `(v,0)` and `(0,w)` with the two inclusion
maps. The proof is intentionally `sorry` at stage 2.

The dependency declarations used are `schemeTangentSpace` and the tangent
space construction supplied by `Sheaf.AlgebraicGeometry.SchemeTangentSpace`,
which in turn records `lem-sc-tangent-space-vector-space` and
`lem-sc-tangent-map-linear`.

Edge cases checked: the statement permits arbitrary schemes, arbitrary field
characteristic, and zero tangent vectors in the two inverse clauses; no
nonemptiness or dimension hypothesis is imposed.

Searches recorded on the node were repeated: LeanFinder query “tangent space
of product scheme is direct sum” (only projection/product candidates), Loogle
query “tangent space product Scheme” (no hits), and grep for
`tangentSpace|TangentSpace|product.*tangent` in pinned Mathlib (no match).

## Earlier second reading (a previous round; superseded)

I reread the node and module. The field and scheme hypotheses correspond to the schemes over k; `TX`, `TY`, and `TZ` are the three tangent spaces. The first conclusion clause gives both projection components, while the second and third clauses give the stated inverse values for `(v,0)` and `(0,w)`. The stage-2 proof remains `sorry`; no statement was proved.

## Second reading by G1

Read the node's statement and all three proof steps, its five statement-dependency
nodes and their recorded signatures, the original module, and Stacks Tag 0BEB
(`varieties-lemma-tangent-space-product`, varieties.tex lines 3124–3150 in the
local Stacks checkout /home/ubuntu/c1-stacks-review; tags/tags confirms the tag).
The Stacks statement allows an arbitrary base S and requires both residue fields
to equal that of the image point. The node correctly specializes to S = Spec k
and k-rational points; it assumes no finite type, smoothness or characteristic
condition. The node itself needs no correction; no statement_change is added.
The earlier second-reading paragraph above is superseded by this reading.

Object/hypothesis/conclusion checklist (the verdicts describe the repaired file):

- A field k: `(k : Type u) [Field k]`. Exact; no finite or algebraically closed
  field instance occurs.
- Arbitrary k-schemes X and Y: `(X Y : Scheme.{u})` and structure morphisms
  `pX`, `pY` into `Spec (.of k)`. Exact, using the explicit structure-map form
  accepted for fibre products and the recorded tangent-space declaration.
- Rational points x and y: sections `sx`, `sy` with `hsx : sx ≫ pX = 𝟙 _` and
  `hsy : sy ≫ pY = 𝟙 _`; `x := sx a`, `y := sy a`, where
  `a := IsLocalRing.closedPoint k`. Exact alternative presentation, without an
  additional hypothesis: a k-rational point is equivalently its unique
  k-morphism Spec k → X. The already-proved source theorem
  `Scheme.Hom.bijective_residueFieldAlgebraMap_of_comp_eq_id` (PointCount.lean
  lines 207–225) supplies the structural residue-field bijections for these
  sections, for arbitrary fields and arbitrary schemes. Its signature has no
  finite-field or finite-type instance. `eX` and `eY` are these bijections as
  ring equivalences, not arbitrarily chosen identifications with k.
- Product over k and its pair point: `P := pullback pX pY`, with canonical
  `prX`, `prY`; `sZ := pullback.lift sx sy (hsx.trans hsy.symm)` and `z := sZ a`.
  Exact; in particular `prX z = x` and `prY z = y` by the projection identities.
  The pairing is itself a section of `pZ := prX ≫ pX`, so z is also rational;
  its rationality is a consequence, never an extra binder.
- The maps (1,y) and (x,1): `iX := pullback.lift (𝟙 X) (pX ≫ sy) ...` and
  `iY := pullback.lift (pY ≫ sx) (𝟙 Y) ...`. Exact, including the two constant
  cross-projections. The small simp terms establish only the compatibility
  needed to form these canonical lifts from hsx/hsy; no lemma is proved.
- Tangent spaces of these exact schemes at these exact points: `TX`, `TY`,
  `TZ` all use the recorded `schemeTangentSpace k ...` declaration. Exact.
  Opened SchemeTangentSpace.lean and read its subtype definition, group and
  module instances, and schemeTangentMap. Also opened TangentVectorsVectorSpace.lean
  and TangentMapLinear.lean: their named existence theorems specify the actual
  canonical operations and postcomposition, rather than arbitrary structures.
- The k-vector space structures: the three `Module.compHom` instances restrict
  the existing residue-field module structures along `rX`, `rY`, `rZ`, the
  structural `residueFieldAlgebraMap`s. Exact; no arbitrary Module hypothesis.
  Opened ZetaSeries.lean lines 216–225 and PointCount.lean lines 62–70 to check
  this structural map's definition and its spectrum characterization.
- Forward map induced by both projections: the first conjunction says
  `v.val ≫ prX = dZX ≫ (e v).1.val` and similarly for Y. Exact. Here `dZX`
  is Spec of the dual-number map of `rZ.comp eX.symm.toRingHom`, and `dZY`
  is analogous. These are the canonical changes from κ(x) and κ(y) to κ(z).
  Indeed the projection residue map composed with rX is rZ, so bijectivity
  of rX determines it as rZ ∘ rX⁻¹; likewise for Y. Thus these equalities
  specify precisely the differentials in the recorded tangent definition,
  without introducing a new tangent map or unconstrained function. Opened
  DualNumbers.lean lines 80–100 to verify the coefficientwise ring-map lift.
- Isomorphism and linearity: `∃ e : TZ ≃ₗ[k] (TX × TY)`. Exact. For two
  vector spaces, the product is the finite direct sum, without finiteness
  assumptions on either space or on its dimension.
- Inverse on (v,0): `(e.symm (v, 0)).val = dZX ≫ v.val ≫ iX`. Exact.
  The equality is on underlying scheme morphisms with a common residue-field
  dual-number source, and subtype extensionality gives equality of vectors.
- Inverse on (0,w): `(e.symm (0, w)).val = dZY ≫ w.val ≫ iY`. Exact, by
  the same identification. Both clauses are universally quantified after e.

Dependency audit: def-weil-pbc-scheme-conventions explicitly fixes no new
notion; Scheme and the displayed structure morphisms render its relevant
convention. def-pc-fibre-product records Mathlib `Limits.pullback`, with
`pullback.lift`, its projection identities and uniqueness; these are exactly
what the module uses. def-sc-scheme-tangent-space records SchemeTangentSpace,
whose canonical vector-space structure is selected from the declaration of
lem-sc-tangent-space-vector-space and whose differential is selected from
lem-sc-tangent-map-linear. The repaired projection and inclusion formulas use
that same postcomposition interpretation with the residue-field transport
written explicitly. None of these dependencies requires repair. No new
notion, new node or dependency module is introduced.

Edge cases: empty X or Y admits no rational point section, exactly as the
node's hypotheses require; nothing extra excludes an empty scheme case. Zero
tangent spaces and zero vectors are allowed and all three displayed clauses
remain meaningful. There is no index-set or dimension parameter, so empty
index sets and n = 0 introduce no further case. All field characteristics are
allowed. The declared universe u is arbitrary, with every variable explicitly
bound; the shared universe is the standard Scheme/Spec convention of the
recorded dependencies, not a small-universe restriction (data can be lifted
to a common universe). There are no Noetherian, finite-type, separatedness,
smoothness, connectedness, or finite-dimensionality assumptions.

Independent searches, with words different from the original worker's query:

- LeanFinder through msearch.py: “Zariski tangent vectors fiber product
  rational points linear equivalence”: eight hits, including
  Scheme.Pullback.carrierEquiv, Triplet.tensor, SpecTensorTo and residue-field
  tensor maps. These describe the underlying points of a scheme pullback,
  not its dual-number tangent vector spaces or this linear equivalence.
- LeanSearch through msearch.py: “The Zariski tangent space of a fiber product
  at rational points is the product of the tangent spaces”: service returned
  Internal Server Error/unavailable. Recorded as unavailable, not as no match.
- Loogle through msearch.py: `AlgebraicGeometry.Scheme, LinearEquiv`: zero hits.
- rg in pinned Mathlib AlgebraicGeometry, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json for tangent with prod/pullback (both orders),
  and the proposed full declaration name: only tangent-sheaf pullback
  results in WeilConjectures/AlgebraicGeometry/TangentSpace.lean and
  GroupScheme/Lie.lean; opened the relevant signatures. They concern sheaves
  along sections, and in places require smoothness, not the arbitrary-scheme
  tangent-vector theorem. No exact existing declaration found. The existing
  SchemeTangentSpace definitions are reused, not duplicated.

Mismatches found and repaired:

1. The original P was arbitrary, with no fibre-product universal property:
   replaced by Mathlib's actual pullback.
2. Original x and y were unused binders; all tangents were at prX z/prY z,
   with no rationality requirement: replaced by rational point sections and
   their actual pairing point.
3. Original iX/iY had only their own projection identities and an equation
   at z, with no constant cross-projection: replaced by the canonical lifts
   built from sx/sy.
4. Original dX/dY/jX/jY were arbitrary functions, never tied to differential
   maps, making the assertion false (even choosing a zero projection function
   on a nonzero tangent space is a counterexample): removed all four binders
   and specified the maps through canonical morphism equalities.
5. Original `≃+` omitted k-linearity: replaced by `≃ₗ[k]` using the canonical
   restricted scalar actions.
6. Original docstring omitted the node's three proof steps, and the file had
   no project header: supplied both and retained only one theorem, with proof
   `by sorry`. There are no definitions with postponed data.

The node's natural-language statement and proof are unchanged. Its lean.statement
is copied verbatim from the repaired signature. All lines are at most 100
characters. Server scompile.py compiled the complete module cleanly (2.7 s),
without warnings. No unbound variable or universe remains.

## Reviewer fix (R-pts1005)

Rationality was given as sections `sx`, `sy` of the structure maps with `x := sx a`, a third
form beside the recorded ones. Restated with points `x : X`, `y : Y` and the H1/K1 `rX` form
(`Function.Bijective rX`, `rX := (StructureSheaf.toStalk k (pX x) ≫ pX.stalkMap x ≫ X.residue x).hom`);
the k-actions on TX, TY, TZ are now `Module.compHom` along these same `rX`, `rY`, `rZ` (not
`residueFieldAlgebraMap`). The k-points `sx`, `sy` are derived as `Spec k ≅ Spec κ(x) → X`;
`iX = (1,y)`, `iY = (x,1)` are the pullback lifts, their compatibility proved in-statement;
`z := iX x` is the point (x,y). Clauses unchanged.
