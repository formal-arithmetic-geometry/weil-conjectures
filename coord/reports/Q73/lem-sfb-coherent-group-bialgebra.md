## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentGroupBialgebra` states
`AlgebraicGeometry.Scheme.Modules.coherentGroupBialgebra`, with one `sorry` and
no other postponed theorem. The natural-language statement, seven-step accepted
split, source and proof dependencies are unchanged. This is a stage-2 delivery:
the previous worker's stage-1 refusal does not apply. The live node was reviewed
PASS for its split by Q159 on 2026-10-23, has no Lean record, and appears in the
stage-2 queue. The maintenance handoff in brief-stage2 section 0 explicitly
instructs such an item to continue through `deliver2.py`. The returned delivery ab460dbe2684 is repaired below (H2).

The small helper definitions in this owning module introduce notation for the
actual recorded cohomology, inclusions, unit, coefficient cup, pullback, and
homogeneous tensor subspaces. They are listed in `lean.declarations`. They have
real data; no object is chosen from an unspecified existence assertion. The canonical structure-sheaf coefficient map now has its own definition node
`def-sfb-tensor-pullback-structure-sheaf-map`, recording the existing plain definition. In particular this module
does not replace signed graded multiplication by the unsigned tensor algebra
multiplication of Mathlib's ordinary `Bialgebra`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A field k: `{k : Type u} [Field k]`. No characteristic or perfectness assumption.
- Group scheme G over k: `G : Over (Spec (CommRingCat.of k))` and `[GrpObj G]`.
  Its structure map is `G.hom`; multiplication is `(MonObj.mul (X := G)).left`.
  Mathlib's chosen over-category tensor is the scheme fibre product, so
  `(G ⊗ G).hom` is its structure map. The identity section is already part of
  `GrpObj` and is used in the natural-language counit proof; no extra arbitrary
  section is quantified in the Lean statement.
- Proper: `[IsProper G.hom]`. Geometrically integral:
  `[GeometricallyIntegral G.hom]`. Neither is replaced by geometric irreducibility
  alone, nor strengthened by an extra smoothness/abelian-variety assumption.
- H^n(G,O_G): `coherentCohomologyDegree G.hom n` is literally
  `scalarCohomology G.hom (SheafOfModules.unit G.left.ringCatSheaf) n`.
  Its carrier is the recorded right-derived module cohomology and its k action
  is restriction along the structure map. No etale/group cohomology is used.
- H = direct sum over n >= 0: `coherentTotal G.hom` is
  `⨁ n : ℕ, coherentCohomologyDegree G.hom n`; `coherentInclusion` is `DirectSum.lof`.
- Cup product with multiplication of O_G coefficients: `coherentCup` is
  `scalarCohomologyCup` followed by `scalarCohomologyMap` of the tensor unitor
  `(λ_ (𝟙_ X.Modules)).hom`. The unitor is the structure-sheaf multiplication,
  sending s tensor t to st. The `mulH` homogeneous-generator equation fixes
  the bilinear multiplication on all of H. The analogous `mulP` equation fixes
  the same cup multiplication on G × G.
- Unital associative graded k-algebra: `mulH` and `mulP` are k-bilinear maps,
  their homogeneous equations put a degree p times a degree q in degree p+q,
  and the two associativity and two-sided unit clauses give the ring laws.
  The additive groups and modules are inherited from the direct sums. The unit
  is `coherentOne`, inclusion of `coherentOneDegree`, which is the inverse
  canonical degree-zero sections comparison applied to the actual section 1.
  The structure k-algebra map is consequently r ↦ r • coherentOne, as required
  by k-bilinearity and the unit equations; it is not an unspecified structure.
- H^0 = k·1: `c : k ≃ₗ[k] coherentCohomologyDegree G.hom 0` with
  `∀ r, c r = r • coherentOneDegree G.hom`. Both bijectivity and normalization
  to the structure-map constant classes are asserted.
- Graded commutativity: the homogeneous `mulH` clause has precisely
  `(-1 : k) ^ (p * q)` and swaps the same two included classes.
- Signed tensor multiplication: `mulT` is k-bilinear, and its equation on
  homogeneous pure tensors is exactly sign `(-1 : k) ^ (q * r)` times
  `(a*d) tensor (b*e)`. Pure tensors and homogeneous inclusions span, so this
  fixes the whole multiplication. Its associativity and unit 1 tensor 1 are
  explicitly included, not postulated as extra hypotheses.
- External cup-product isomorphism κ: `κ` is a k-linear equivalence from
  `H ⊗[k] H` to `coherentTotal (G ⊗ G).hom`. Its pure-generator equation is
  projection pullbacks with the canonical structure-sheaf coefficient maps,
  followed by `coherentCup` in degree p+q. This is exactly the external cup
  after the canonical coefficient identifications. It fixes κ uniquely, gives
  its grading, and rules out an arbitrary vector-space equivalence. The next
  two equations say that κ preserves the signed product and the unit. Since
  the decompositions are direct and κ is bijective, its inverse also preserves
  each total degree; no choice of a different grading is possible.
- m*: `pullM` is linear and its homogeneous equation uses `coherentPullback`
  of the actual group multiplication, with the over-morphism commutativity
  equation as its proof that multiplication is over k.
- Δ = κ⁻¹m*: `Δ = κ.symm.toLinearMap.comp pullM`. The quantified linear maps
  are fixed by these homogeneous-generator formulas, not assumed inputs.
- Degree preserving Δ: its value on degree n lies in `coherentTensorDegree`,
  the k-span of pure tensors of degrees p,q with p+q=n. This is the ordinary
  total tensor grading, with finite sums, including the degree-zero case.
- Unital and multiplicative Δ: the equations are Δ(1)=1 tensor 1 and
  `Δ (mulH x y) = mulT (Δ x) (Δ y)`, using precisely the signed multiplication.
- Coassociativity: `TensorProduct.assoc` transports `(Δ tensor id)(Δ x)` to
  the same parenthesization as `(id tensor Δ)(Δ x)` for every x.
- ε is projection onto H^0=k: `ε` is `c.symm` composed with
  `DirectSum.component ... 0`. Thus ε is the actual degree-zero projection,
  not an arbitrary linear functional.
- Both counit equations: `TensorProduct.map ε LinearMap.id` followed by
  `TensorProduct.lid`, and `TensorProduct.map LinearMap.id ε` followed by
  `TensorProduct.rid`, each applied to Δ(x), equal x for every x.
- Every degree-one class primitive: the final universal equation is
  Δ(inclusion x)=inclusion x tensor 1 + 1 tensor inclusion x.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`, the `def-weil-field` Mathlib match.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` and its
  inherited `MonObj`; `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`
  documents exactly this specialization for group schemes and imports its
  chosen over-category product infrastructure.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`:
  `AlgebraicGeometry.GeometricallyIntegral` (with the recorded irreducible and
  reduced specializations). The full signature, class docstring and inherited
  properties were read; geometric integrality is exactly the clause used.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`:
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`, and its recorded
  `RingedSpace.moduleCohomology` conventions.
- `WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`:
  `scalarCohomology`, `scalarCohomologyCarrier`, `scalarCohomologyModule`,
  `scalarCohomologyCup`, `scalarCohomologyMap`, `scalarCohomologyPullback`.
  Their full signatures and docstrings were inspected, as were `externalCup`
  and `externalCupCoefficients` to check the projection-cup normalization.
- `WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison`:
  `scalarGlobalSectionsEquiv`, the existing declaration of
  `def-sc-scalar-global-sections-comparison`, fixes the unit class to section 1.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`:
  `tensorPullbackObjUnitToUnit`, owned by the new definition node
  `def-sfb-tensor-pullback-structure-sheaf-map`. Its definition is the adjoint
  of the actual structure-sheaf morphism under the canonical tensor adjunction.
  The separate `tensorPullbackObjUnitToUnit_isIso`, recorded by
  `lem-weil-pbc-module-pullback-structure-sheaf`, remains a proof dependency.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible` supplies the published
  scheme-module tensor instance (the same sheafified tensor product used by
  the recorded operations), used with `X.Modules` to expose the unitor.
- Mathlib direct-sum `lof`/`component` and module tensor `map`/`assoc`/`lid`/`rid`
  give the ordinary linear algebra of the statement, with no private copies.

The existing landed degree-zero comparison node and the new definition node
for the canonical structure-sheaf pullback map are added to `stmt_deps`.
The structure-sheaf isomorphism theorem is retained only in `proof_deps`. No node statement, split, proof, proof-dependency list or
maintainer review record is changed. All currently recorded proof-dependency
modules are imported, with proof-only visibility. The new cup-associativity
proof node has no recorded module and is therefore not imported; stage 2 does
not wait for proof dependencies. The complete seven-step proof is retained in
the theorem docstring.

Edge cases checked before writing: characteristic two (the sign becomes 1 but
no odd-square vanishing is asserted); imperfect fields (no perfectness used);
G=Spec k (only degree zero, Δ and counit give their tensor-unit maps); degree
zero and p=0/q=0 (the exact sign and unit formulas still apply); zero positive
cohomology; finite-support sums versus infinite products. The empty scheme is
excluded by the group identity section, not by an added hypothesis. Universes
are explicitly bound; field and schemes have the project's standard shared
universe u, with modules `ModuleCat.{u}` as in the dependency interfaces.
`autoImplicit` is false. Every theorem has only `sorry` as proof.

Source reading: Stacks `varieties.tex`, lemma-kunneth, Tag 0BED explicitly
constructs the map by projection pullbacks and cup product. Stacks
`cohomology.tex`, lemma-cup-product-associative and
lemma-cup-product-commutative provide the associator and signed symmetry. Milne
AV I printed p.55 (PDF page 61), the paragraph immediately before Lemma 12.2,
gives the group-law coproduct and identity-slice calculation. Its etale context
is explicitly identified as an adaptation in the node and module; neither
Milne's later perfect-field hypothesis nor his exterior-algebra conclusion is
asserted here. The current blueprint's direct-image proof and inherited
auxiliary ancestry were inspected; this is not the unit's own statement.

Searches (all on 2026-10-23):

- `msearch.py ... leanfinder`: "The coherent cohomology of a proper geometrically
  integral group scheme is a graded bialgebra via cup product and multiplication
  pullback" returned eight hits on groupCohomology, continuous group cohomology,
  and ordinary Bialgebra GroupLike operations. None is coherent sheaf cohomology.
- `msearch.py ... loogle 'Bialgebra, GradedAlgebra'`: zero hits.
- `msearch.py ... grep 'cohomology.*(bialgebra|hopf)|(bialgebra|hopf).*cohomology'`:
  one background-comment hit in `Mathlib/Topology/Homotopy/HSpaces.lean`.
- `msearch.py ... leansearch`: "Coherent cohomology of a proper algebraic group is
  a connected graded bialgebra with coproduct from multiplication" returned eight
  ordinary unsigned Bialgebra declarations, including `Bialgebra.mk'` and
  `Bialgebra.comul_mul`; none states the signed coherent result.
- `rg` in the project's `lean/WeilConjectures` and `lean/Sheaf`, and
  `grep -rn 'lem-sfb-coherent-group-bialgebra' lean/WeilConjectures`: no existing
  coherent-group-bialgebra declaration. Existing scalar cohomology, cups,
  pullback maps, and global-section comparison were found and reused.
- `rg` of every new declaration name in Mathlib, `WeilConjectures`, `Sheaf`,
  and `dag/lean_names_upstream.json`: the first proposed name `coherentCohomologyDegree`
  was originally `coherentDegree`, which already means a coherent module degree on
  curves. It was renamed before delivery. No final declaration name collides.

No `STATEMENT-DISPUTED` issue or statement correction is needed. The new node records an existing upstream definition, so no new or
repaired dependency module is delivered. The first server compiler checks
identified notation scope, the explicit scheme-module tensor unit, and the
orientation of the second projection's base-commutativity equality; these were
fixed. The final file compiles on the server cleanly, in both sandbox and real
module mode, including the recorded proof imports. Only the expected postponed
statement remains.


## New nodes

`def-sfb-tensor-pullback-structure-sheaf-map` defines, for every scheme morphism
`g : X ⟶ Y`, the canonical coefficient morphism `g^* O_Y ⟶ O_X` adjoint to
`g sharp`. Its source is Stacks Tag 0096 (the canonical Hom adjunction), with
the tensor-formula pullback of Tag 0095. The existing upstream declaration is
`AlgebraicGeometry.Scheme.Modules.tensorPullbackObjUnitToUnit` in
`WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`; the node
records `existing: true` and adds no Lean module. The binder `{X Y : Scheme.{u}}`
and `(g : X ⟶ Y)` render arbitrary scheme morphisms; the result type is the
pullback of `SheafOfModules.unit Y.ringCatSheaf` mapping to
`SheafOfModules.unit X.ringCatSheaf`. The definition body is exactly
`homEquiv.symm` applied to `unitToPushforwardObjUnit g.toRingCatSheafHom`,
using `Classical.choose (exists_tensorPullbackAdjunction g)`. Thus the map is
pinned to `g sharp`; neither an isomorphism proof nor an arbitrary coefficient
morphism is supplied as data. This works for identity maps, maps of empty
schemes, and arbitrary schemes without properness or field assumptions.

The new searches are preserved verbatim from `msearch.py` in the node's
`mathlib_searches`: LeanSearch for the canonical adjoint structure-sheaf map
found 8 hits including Mathlib `SheafOfModules.pullbackObjUnitToUnit`;
Loogle for that name found 6 hits; Mathlib grep for the two unit-map definitions
found the definitions on lines 60 and 86 of `PullbackFree.lean`. Those use
Mathlib's abstract pullback, whereas the exact tensor-formula map is already
upstream on line 33 of `TensorPullbackStructureSheaf.lean`. Searches of the DAG,
`lean/WeilConjectures` and `lean/Sheaf` found uses and the isomorphism theorem,
but no definition node owning this map. The existing HOver linear-cohomology
map is a different interface. `blueprint_refs.py search 'structure sheaf'`
returned 19 blueprint hits, none defining this coefficient map; `ancestor`
reports the inherited null blueprint ancestor. The three dependencies are
`def-pc-scheme`, `def-pc-module-pullback`, and
`def-weil-sheaf-of-modules-category`, as requested in the return.

## Repair of return H2

The independent review of immutable head `ab460dbe2684` accepted the mathematics
and returned only definition-node ownership of `tensorPullbackObjUnitToUnit`.
The saved packet first passed the required dry run at `799c45f48f3` before this
repair. The repair replaces the theorem
`lem-weil-pbc-module-pullback-structure-sheaf` in the item's `stmt_deps` by
`def-sfb-tensor-pullback-structure-sheaf-map`; the theorem remains unchanged in
`proof_deps`. No theorem or definition is restated. The item's statement,
proof, proof dependencies and Lean record remain unchanged. Its Lean file is
byte-identical to the saved returned packet (SHA-256
`bf499b5e85d6c76296801b1cdd3e40c783d6c92afe7aa4cd9652b44940d98d8f`).
The read clone was compared field by field with the saved packet, and the
prescribed delivery wrapper rebases the packet on current live `sheaf-dag`.
The current server source was read with `scompile.py --source` and agrees with
the recorded definition and its exact signature. No statement correction is
needed. Compilation and preflight are repeated on the repaired packet.

The repaired-packet dry run required the live schema key `import_flags`; the
new node now has `import_flags: []`. Its upstream branch metadata follows the
preflight convention `slopmaster2` for a `WeilConjectures` declaration. The
server source remains the live published module read above.

## Second reading by Q73

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
