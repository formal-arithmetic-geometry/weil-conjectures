## Worker report

The delivery states `AlgebraicGeometry.Scheme.Modules.coherent_frobenius_comparison`
in `Sheaf.AlgebraicGeometry.CoherentFrobeniusComparison`. Its only proof is `sorry`.
The companion module constructs the missing canonical comparison family and transports
additive coefficient endomorphisms through the existing fixed common-resolution comparison.
No definition contains `sorry` data. The existence-and-uniqueness theorem needed by that
construction is separately named, has its full natural-language proof, and belongs to the
new definition node. The main theorem's docstring contains all six original proof steps.

Hypotheses and named objects, clause by clause:

- A prime p and characteristic-p field k: `(p : ℕ) [Fact p.Prime] [CharP k p]` and
  `{k : Type u} [Field k]`. The degree is `(q : ℕ)`, including zero.
- Proper k-scheme X: `{X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]`.
  The explicit structure map is used in base change and in the recorded scalar-cohomology API.
- Associated structure sheaf G_X: `structureTensorEtaleSheaf X` is exactly the recorded
  `etaleTensorSectionsSheaf (unit X)`, followed by the existing `uliftFunctor` on coefficients.
  The coefficient lift is needed because the recorded etale inverse-image API uses
  `AddCommGrpCat.{u+1}`. It is the same sheaf under the canonical coefficient-universe
  equivalence; it is not a new model of regular functions. `tensorPullbackObjUnitToUnit`
  identifies its tensor-section presentation with regular functions on an etale object.
- The pth-power maps are `FrZ`, `FrZK`, `FrE` together with `hFrZ`, `hFrZK`, `hFrE`.
  Each is an additive sheaf morphism uniquely specified on every section by pth power.
  The explicit `@id Γ(U.unop.left, ⊤)` in `hFrE` changes only the displayed type from
  unit-module sections to the definitionally identical ring-section type, enabling powers.
  These binders present the named Frobenius maps, rather than assuming any compatibility
  of their cohomology actions.
- E_X^q: `scalarCohomology f (unit X) q` is the existing field-module structure on
  `((RingedSpace.moduleCohomology X.toRingedSpace q).obj (unit X))`.
- F_X^q: `structureCoherentFrobenius f q FrZ` conjugates `Sheaf.H.map FrZ q` by
  `moduleAbelianCohomologyLarge`, itself the recorded fixed common-resolution
  `moduleCohomologyExtResolutionEquiv` followed only by the canonical Ext universe change.
  Its type is `E →+ E`; therefore the requested additivity is part of the object itself.
- c_X^q: `structureCoherentEtaleComparison f q` is the inverse of this same module/abelian
  comparison followed by the uniquely normalized Zariski-to-etale delta-functor comparison.
  It is an additive equivalence, not an unconstrained isomorphism supplied by a hypothesis.
- Every field extension: `{K : Type u} [Field K] [Algebra k K]`. No finiteness,
  algebraic-closure or perfectness hypothesis is imposed. The ring map of a field algebra
  is injective automatically, so this presents an arbitrary field extension.
- X_K and its projections: `(g : Y ⟶ Spec (.of K)) (j : Y ⟶ X)` with
  `h : IsPullback j g f (Spec.map (CommRingCat.ofHom (algebraMap k K)))`.
  Any pullback presentation is allowed. Properness of g is derived from h inside the
  comparison specialization, and is not an additional assumption.
- u: the binder `u` has the recorded `Etale.upperStar` inverse-image type; `hu` states
  on every section that its adjoint under `Etale.upperStarLowerStarAdjunction` is the
  structural ring pullback `(pullback.fst U.hom j).appTop`, using the same tensor-to-unit maps.
  This determines u uniquely. No cohomological compatibility is assumed.
- P_j^q is the explicit composite `Sheaf.H.map u q (Etale.cohomologyMap j G_X q x)`.
- b_q: the `K`-linear equivalence `b` is characterized by `hb` on `1 ⊗ v` as the actual
  recorded `moduleCohomologyFMap j (unitToPushforwardObjUnit ...) q`. By K-linearity,
  this pins its value on every pure tensor to structural coherent pullback multiplied by
  its K coefficient; those tensors generate. Thus b is the canonical flat base-change
  isomorphism named by the node, not an arbitrary existence witness. As explicitly permitted
  by proof step 1, tensor order is commuted: Lean `K ⊗[k] E` and `b (a ⊗ v)` mean
  the paper's `E ⊗[k] K` and `b_q(v ⊗ a)` via `TensorProduct.comm`.

Conclusions, clause by clause:

- Additivity: `structureCoherentFrobenius` returns an `AddMonoidHom`.
- p-semilinearity: the first conjunct is
  `∀ a v, structureCoherentFrobenius f q FrZ (a • v) =
  a ^ p • structureCoherentFrobenius f q FrZ v`.
- Frobenius comparison: the second conjunct is
  `c_X (Sheaf.H.map FrE q x) = F_X (c_X x)` for every etale class x.
- Pullback comparison: the third conjunct is
  `c_Y (Sheaf.H.map u q (Etale.cohomologyMap j G_X q x)) = b (1 ⊗ c_X x)`.
- Field-extension Frobenius: the last conjunct is
  `F_Y (b (a ⊗ v)) = b ((a ^ p) ⊗ F_X v)` for every v and a.

Dependency declarations used (module and name):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`.
- `def-pc-field-characteristic`: Mathlib leaf `{'declaration': 'CharP, ringChar', 'file': 'Mathlib/Algebra/CharP/Defs.lean', 'how': 'exact: `CharP k p` (class, line 46) is `∀ x : ℕ, (x : k) = 0 ↔ p ∣ x`, the defining property of the node; such p exists uniquely (`CharP.existsUnique`, line 145) and is `ringChar k` (line 153, `ringChar.spec` line 158). Lines read with sed -n 2026-10-10'}`.
- `def-sc-etale-qcoherent-module`: `Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf`, `AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsSheaf`.
- `pqf-def-cohomology`: `Sheaf.Paper.PQFCohomology`, `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`.
- `def-sc-zariski-cohomology`: `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`, `CategoryTheory.Sheaf.H'`.
- `lem-sc-module-abelian-zariski-cohomology`: `Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural`, `AlgebraicGeometry.zariskiModuleAbelianCohomologyNatural`.
- `lem-sc-etale-zariski-qcoh-comparison`: `Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison`, `AlgebraicGeometry.Scheme.Modules.etale_zariski_qcoh_comparison`.
- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`.
- `def-pc-base-change`: `Sheaf.AlgebraicGeometry.BaseChangeConventions`, `AlgebraicGeometry.Scheme.Modules.moduleBaseChange`.
- `def-weil-pbc-inverse-image`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, `AlgebraicGeometry.Etale.upperStar`.
- `def-weil-pbc-cohomology-pullback`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`, `AlgebraicGeometry.Etale.cohomologyMap`.
- `lem-sc-flat-base-change-coherent`: `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`, `AlgebraicGeometry.Scheme.Modules.nonempty_H_pullback_linearEquiv`.
- `def-pbc-canonical-coherent-etale-comparison`: companion `Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison`;
  `canonicalCoherentEtaleComparison`, `structureCoherentEtaleComparison`,
  `structureCoherentEtaleComparisonOfPullback`, `structureCoherentFrobenius`.
- `def-sc-field-linear-module-cohomology-operations`: `Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`, `AlgebraicGeometry.Scheme.Modules.scalarCohomologyCup`.
- `lem-weil-pbc-module-pullback-structure-sheaf`: `Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf`, `AlgebraicGeometry.Scheme.Modules.tensorPullbackObjUnitToUnit_isIso`.
- `def-weil-pbc-module-cohomology-fmap`: `Sheaf.AlgebraicGeometry.ModuleCohomologyFMap`, `AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap`.

The companion also reuses `Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality`,
`moduleCohomologyExtResolutionEquiv` (node
`new-module-cohomology-ext-resolution-naturality`), read from the server's published source
because that landed module is absent from the local Lean snapshot. It uses the actual
Mathlib `Sheaf.H`, `Abelian.Ext.comp`, `ShortComplex.ShortExact.extClass`,
`Abelian.Ext.homAddEquiv`, and the existing coefficient-lift functor. There is no private
copy of cohomology, tensor pullback, field scalar action, or module/abelian comparison.

Edge cases checked: q=0 (normalization is the tensor-pullback unit on sections); empty X
(all section/cohomology groups have their ordinary zero-object interpretation); zero
cohomology groups; p=2; arbitrary imperfect k and K; K=k and the identity pullback;
non-smooth proper schemes; no curve, dimension, connectedness or algebraic-closure
hypothesis. Natural-number degrees and a same-universe field extension lose no geometric
case: objects may be placed in any sufficiently large universe. No disputed statement or
node correction was needed.

Searches for the main item: msearch LeanFinder query “The canonical etale coherent
cohomology comparison commutes with Frobenius and flat field extension” returned eight
unrelated formally-etale results; Loogle query `"Frobenius", "cohomology"` returned zero;
msearch grep `Frobenius.*cohomology|cohomology.*Frobenius` returned zero. Searches of
WeilConjectures for the node id returned zero. `rg Frobenius` in lean/Sheaf located
ArtinSchreierFrobeniusExactRows, whose curve-specific existential comparison is not this
statement. The source places were read in local Stacks etale-cohomology.tex (03P2 and
0A3P), sites-cohomology.tex (03FD), and coherent.tex (02KH).

## New nodes

`def-pbc-canonical-coherent-etale-comparison` introduces the uniquely normalized
Zariski-abelian-to-etale comparison on quasi-coherent modules of a proper scheme over a
field, composes it with the existing fixed resolution comparison, and defines the
transported additive action and structure-module specializations. Sources: Stacks
03P2, 03FD, 010S and the Frobenius use in 0A3P. Naturality alone does not identify a
comparison in positive degrees: the connecting-map condition and normalization make
the whole family unique by universality of the effaceable delta functor on QCoh.
Accordingly, the definition chooses from a unique-family theorem, not a mere existence
claim with undetermined data. That theorem is the only auxiliary sorry.

Searches: msearch LeanSearch for the unique normalized morphism of delta functors
returned UNAVAILABLE (Internal Server Error); this is recorded honestly in mathlib_searches.
Loogle `"delta", "cohomology"` returned zero. Grep/rg for normalizedCoherentEtale,
IsNormalizedCoherentEtaleComparison, canonical etale comparison and uniqueness in
Mathlib, WeilConjectures, and lean/Sheaf found no such definition. Existing
EtaleZariskiQcohComparison is reused for its uniquely component-determined coefficient
maps; its existential cohomology comparison has no connecting-map normalization.
`tools/blueprint_refs.py search "canonical coherent"` found zero blueprint nodes;
DAG searches found no normalized-comparison definition. Existing comparison nodes are
cited rather than copied. The new node is cited in the item's stmt_deps.

Validation uses only scompile.py on the server, nice 19, two threads, 60 seconds per
file, compiling the companion before the main theorem. No local compiler or lake build
was invoked. The delivery dry run is run with --no-push; the second reader delivers.

## Second reading by NE

I independently read the item node, both delivered modules, the new definition node,
and the source passages 0A3P, 03P2, 03FD, 02KH and 010S. The list of objects,
hypotheses and conclusions in the original node matches the Lean as follows.

1. Prime p and characteristic-p field k: `p : ℕ`, `Fact p.Prime`, `Field k`,
   `CharP k p`. Exact. The source 0A3P assumes algebraic closure for its subsequent
   finiteness and Artin-Schreier argument; the comparison and base-change statements
   extracted here use 03P2 and 02KH, which require no algebraic closure.
2. Proper k-scheme X: `X : Scheme.{u}`, `f : X ⟶ Spec (.of k)`, `IsProper f`.
   Exact; finite type, separatedness and quasi-compactness follow from properness.
3. Associated structure sheaf G_X: `structureTensorEtaleSheaf X` unfolds to the
   recorded `etaleTensorSectionsSheaf (unit X)` with standard coefficient ULift.
   Exact. I opened EtaleTensorSectionsSheaf and TensorPullbackStructureSheaf:
   `tensorPullbackObjUnitToUnit` is adjoint to the structural ring map, and its
   isomorphism theorem identifies each tensor section with a regular function.
4. Additive sectionwise Frobenius: `FrZ`, `FrZK`, `FrE` with `hFrZ`, `hFrZK`,
   `hFrE`. Exact: these specify the named coefficient maps on all sections,
   rather than assuming any of the desired cohomology identities. The etale
   condition uses the structure-pullback isomorphism before taking pth powers.
5. Every nonnegative degree: `q : ℕ`. Exact, including degree zero.
6. E_X^q: `scalarCohomology f (unit X) q`. Exact. I opened its definition:
   its carrier is the recorded `RingedSpace.moduleCohomology`, and its k-action
   is restriction along `scalarMap f ⊤`, not a new cohomology theory.
7. Transported Zariski Frobenius F_X^q: `structureCoherentFrobenius f q FrZ`.
   Exact: it conjugates `Sheaf.H.map FrZ q` through `moduleAbelianCohomologyLarge`.
   I read the published `moduleCohomologyExtResolutionEquiv` signature and
   construction: it is the common-resolution comparison, followed here only by
   canonical Ext universe transport. The existential natural isomorphism in
   ZariskiModuleAbelianCohomologyNatural alone would not specify this map.
8. Canonical inverse comparison c_X^q: `structureCoherentEtaleComparison f q`.
   Exact: it inverts the fixed module/abelian comparison followed by the unique
   normalized change-of-site family. The family is natural in quasi-coherent
   module maps, has the tensor-unit normalization in degree zero, and commutes
   with connecting homomorphisms. The latter condition is essential for uniqueness.
9. Every field extension: `K : Type u`, `Field K`, `Algebra k K`. Exact;
   a unital map from a field to a field is injective. No perfectness or finiteness.
10. Base change and projection: `Y`, `g`, `j`, and `IsPullback j g f (Spec.map ...)`.
    Exact, allowing every presentation of the pullback. The companion derives
    properness of g by base-change stability, rather than assuming it.
11. Coefficient map u: the recorded `Etale.upperStar` binder and `hu` using
    `upperStarLowerStarAdjunction`. Exact. I read both APIs: its adjoint evaluates
    on the actual etale base-change functor, and `hu` specifies structural pullback
    by `(pullback.fst U.hom j).appTop` after the tensor-unit identifications.
12. P_j^q: `Sheaf.H.map u q (Etale.cohomologyMap j ... q x)`. Exact. I opened
    cohomologyMap: it is inverse image of Ext classes with the constant-sheaf
    comparison, not an arbitrary map or an inverse-image/coefficient isomorphism.
13. Canonical b_q: `b : (K ⊗[k] E_X) ≃ₗ[K] E_Y` and `hb` specifying its
    value at `1 ⊗ v` as `moduleCohomologyFMap j (unitToPushforwardObjUnit ...) q`.
    Exact: K-linearity determines all pure tensors and hence the entire map.
    The exchanged tensor order is the canonical commutativity equivalence.
    I read ModuleCohomologyFMap's resolution construction and the recorded upstream
    flat-base-change theorem. The latter only provides `Nonempty` of an equivalence
    on its Ext presentation, so choosing that witness would not pin b_q. The
    delivered `hb` correctly pins the genuine coherent pullback instead.
14. Additivity of F_X: the codomain of `structureCoherentFrobenius` is `→+`.
    Exact, encoded in the type rather than a redundant conjunct.
15. p-semilinearity: the first conjunct is `F_X (a • v) = a ^ p • F_X v`.
    Exact for every a in k and every v in E_X.
16. Frobenius comparison: second conjunct `c_X (H(FrE) x) = F_X (c_X x)`.
    Exact, for every etale cohomology class x.
17. Pullback comparison: third conjunct `c_Y (P_j x) = b (1 ⊗ c_X x)`.
    Exact, for every x and the specified pullback presentation.
18. Frobenius after scalar extension: final conjunct
    `F_Y (b (a ⊗ v)) = b ((a ^ p) ⊗ F_X v)`. Exact for every v and a in K.

The named-map binders specify objects introduced in the node; they add no geometric
hypothesis. Their equations uniquely determine them. All variables and the universe
are bound explicitly. The same universe covers arbitrary field extensions and schemes
by choosing a common sufficiently large universe; there is no small-universe test
quantifier. Edge checks: q=0 uses precisely the normalization on global sections;
empty schemes and zero cohomology groups retain their usual zero objects; the zero
section ring on an empty open is allowed; p=2 is included; p=0 and p=1 are correctly
excluded by primality. No index family is quantified here, so an empty covering is
not excluded. Identity extension K=k, imperfect fields, disconnected and nonreduced
proper schemes are covered. The statement imposes no smoothness or dimension condition.

New-node reading: def-pbc-canonical-coherent-etale-comparison describes precisely
what its companion defines. Its restriction to proper schemes matches this definition
node and suffices here. On a proper scheme over a field, quasi-coherent sheaves form
an abelian category, their sheaf cohomology is an effaceable delta functor, and 03P2
identifies the etale theory. Thus 010S gives uniqueness after degree-zero normalization;
03FD supplies the module/abelian identification. The ShortExact/extClass condition
in `IsNormalizedCoherentEtaleComparison` expresses the connecting maps of those actual
abelian sheaves. The extra zero-composite and exactness proof arguments are available
for every such sequence by exactness of etale pullback and forgetting modules, so do
not restrict the sequences covered. `Classical.choose` selects from an `∃!` theorem,
which determines the whole family, not from an underdetermined existence assertion.
`coherentEtaleMap` uses the existing comparison theorem's component-determined map;
its displayed component formula determines it uniquely as well. All other new data
are composites, restrictions or transports of those objects. There is no hollow
definition, private substitute, local notation or local instance in either delivery
module. Every theorem in the delivery has only `sorry`; both theorem docstrings give
their natural-language proofs and source tags. The main theorem retains all six node
proof steps. No dependency module or statement correction is needed.

Independent searches: msearch LeanFinder for naturality of the canonical etale/Zariski
structure-sheaf comparison under absolute Frobenius returned eight generic structure
sheaf/global-section naturality results, no match. Loogle `"cohomology", "frobenius"`
returned zero hits. LeanFinder for a unique natural isomorphism of the etale and Zariski
cohomological delta functors normalized in degree zero returned eight formally-etale
cotangent results, no match. Direct rg searches in Mathlib, WeilConjectures and
lean/Sheaf found no normalizedCoherentEtale/IsNormalizedCoherentEtaleComparison/
canonicalCoherentEtaleComparison declaration. Broader Frobenius/cohomology searches
found Weil/l-adic material and the ArtinSchreier curve modules; I opened
ArtinSchreierBaseChangeModel and verified its smooth connected algebraically closed
curve/degree-one existential model is not this statement. DAG searches found only
the existing existential comparison nodes, not this normalized-family definition.
The worker's LeanSearch unavailability remains recorded honestly, without fabricated hits.

Repairs: the new definition node lacked the required `proof: []` field; added it.
The item had added three already existing nodes to `stmt_deps`, contrary to the rule
allowing only new definition nodes there without a statement correction; restored
those entries to the base list and kept the genuinely new canonical-comparison node.
The actual dependencies and imports remain reused: scalar cohomology is cited through
the new definition node, and the existing cohomology-fmap is already a proof dependency.
No Lean signature, definition, node statement or proof was changed. Both recorded
`lean.statement` strings were checked against their respective source signatures.

Validation: both delivered files compiled separately through scompile.py on the server,
nice 19, two threads, limit 60 seconds per file: companion 49.4 s, main 2.1 s, no
warnings or errors. The delivery dry run and delivery repeat the required checks.
