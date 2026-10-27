## Worker report

The module `Sheaf.Paper.CompatibleKummerTowerCech` states
`AlgebraicGeometry.ProEtale.KummerCech.compatible_kummer_tower_cech`, with `sorry`.
Its helper structures `Coordinates` and `Substitution` package the clauses of this
same theorem; their data are not chosen from an existence theorem. Every helper
has a source/blueprint docstring. All universes and variables are explicitly bound.
No statement correction or dependency repair was needed. The returned delivery is repaired below; a new existing-declaration definition node now owns the root-coordinate views.

Source read: ILO, Travaux de Gabber, IX Proposition 2.1, printed pp.133–134
(PDF pages 139–140), especially the displayed simultaneous root quotient and the
natural root-of-unity action. The CRT, adic reconstruction, compatible limit and
unit-substitution calculations are the agent-written supplement in the assigned
node, not claims that the book states this entire general-ring lemma. Also read
the current blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/_section.md` and its direct-images proof, paragraph (3).
The entire eleven-step DAG proof appears in the theorem docstring.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Prime p | `(p : ℕ) (hp : p.Prime)` |
| Commutative H, characteristic p | `{H : Type u} [CommRing H] [CharP H p]`; no additional nontriviality assumption |
| r ≥ 0 and t_1,...,t_r | `(r : ℕ) (t : Fin r → H)` |
| All positive n prime to p | Existing `TameRootOrder p = {n : ℕ // 0 < n ∧ n.Coprime p}` |
| Fixed primitive ζ_n | `ζ` and `hζ` |
| Compatible roots under n dividing m | `hcompat` |
| Unit difference for distinct residue classes | `hunit`, quantified over `a b : ZMod n.val` |
| f is the product, including f=1 for no parameters | `∏ i, t i` and `Localization.Away (∏ i, t i)` |
| Finite X_n = Spec of the specified localized quotient | `cover t (some n)`, using existing `view p t (some n) none true`, `stage`, `Algebra.pthRootAlgebra`, and `viewMap` |
| Γ_n = (Z/n)^r, with addition written multiplicatively | `Label p r (some n) = Multiplicative (ULift (Fin r) → ZMod n.val)` |
| Power transitions | `Coordinates.transition_root`, `transition_coeff`, `transition_id`, `transition_comp` |
| Reduction transitions for Γ | `reduction n m h`, coordinatewise `ZMod.castHom` |
| X is the inverse limit | `cover t none` is the actual localized `tameRootAlgebra p t`; `inclusion_root`, `inclusion_coeff`, `inclusion_transition` and `limit` state its projections and full universal property against arbitrary schemes |
| G = product of q-adic integers, once per parameter | Existing `ParameterRootDeckGroup p (ULift (Fin r))`, as `Label p r none` |
| Usual topological residue identification with lim Γ_n | `characters : ParameterRootCharacters ... H` includes continuous monoid-hom residues and normalization on every integral vector. `residueHomeo` is a homeomorphism to the compatible residue families, and `residue_eq` fixes its exact coordinates |
| X[P] is the specified profinite test object | Existing `profiniteProduct`, definitionally `((profiniteToProEtOf X).obj P).left`; its base, section and map are the recorded interfaces of `def-sfb-profinite-product-maps` |
| Root rotations | `rotation_root` gives exactly ζ_n^(a_i) x_i; for full labels `exponent` uses the fixed residue of that label at the root's own order. `rotation_coeff` fixes coefficients |
| These are compatible actions | `rotation_one`, `rotation_mul`, `rotation_transition`, `rotation_inclusion`. The group inverse and these identities also give inverse rotations; the comparison's second projection is the scheme-valued action |
| Finite and full scheme comparisons are isomorphisms | `comparison k` is an actual scheme isomorphism, for both `some n` and `none`. For a finite discrete label space, the recorded definition of X[P] identifies its domain canonically with the finite disjoint union of X_n. This uses the existing finite-test-object presentation, not an arbitrary cover |
| First comparison projection is x | `comparison_fst` |
| Second comparison projection is gx | `comparison_slice`, as equality of scheme morphisms on every fixed label, with the algebra rotation already fixed on every generator |
| Compare at all divisibility levels and at the limit | `comparison_transition`, `comparison_inclusion`. The first projections commute by `comparison_fst` and the recorded functorial product map; the equations explicitly record the second projections |
| Triple vertices (x,gx,hgx), direct label hg | `tripleComparison` is the scheme isomorphism to the pullback of the two double overlaps along their second/first vertex maps. `tripleComparison_fst` fixes its first edge to (x,gx); `tripleComparison_snd` fixes its second edge to (gx,hgx). `triple`: `nextVertex` sends (x,g,h) to (gx,h), and `composedLabel` sends (g,h) to h*g. Their subsequent action arrows agree as scheme maps on X[G×G], not only as identities on geometric points. The same field is imposed at every finite level |
| General target ring of characteristic p and its compatible roots | The quantified `K`, instances, `s`, `η`, `_hη`, `_hcompat`, `_hunit` in the theorem conclusion |
| Ring map preserves roots | `φ`, `_hroots` |
| φ(t_i)=u_i t'_i, with units u_i | `unit : Fin r → Kˣ`, `_ht` |
| Compatible roots v_(i,n) of u_i | `v`, `_hv`, `_hvcompat`; no extra hypothesis that v is a unit is needed |
| Substitution x_(i,n) ↦ v_(i,n) x'_(i,n) | `Substitution.map_root` at both finite and full levels; `map_coeff` fixes the specified coefficient map |
| Substitution extends to punctured base | `baseMap`, `baseMap_coeff`, `base_natural` |
| Substitution commutes with divisibility maps and the limit | `transition_natural`, `inclusion_natural` |
| Both comparison projections commute | `Substitution.comparison_fst` and `comparison_snd` |
| Every rotation coordinate commutes | `rotation_natural` at every finite/full level; `residue_eq` fixes the identical residue coordinates on source and target |
| Ordinary parameter-preserving base change | Specialize `unit` and `v` to constant 1. The substitution formula becomes x_i ↦ x'_i and `_ht` becomes φ(t_i)=s_i. The theorem therefore includes exactly these base-change squares |
| r=0: comparisons are identities and G=1 | `empty_base` says all structural base maps are bijective, `empty_group` makes the full group a singleton, and `empty_comparison` makes the second comparison projection the first. Under the canonical singleton/self-product identifications this is exactly the identity comparison |

The universe lift on the finite parameter index is essential: `Fin r` lives in
`Type`, whereas the existing q-adic group/test-object API uses `Type u` indices
for `Scheme.{u}`. `ULift.{u} (Fin r)` has precisely the same finite coordinates;
`exponent` accesses the coordinate at `⟨i⟩`. It adds neither a size assumption nor
an equality of independent universes. Finite labels remain finite and discrete.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.profiniteToProEtOf`, `profiniteToScheme`, `toSpecZ`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.GroupTheory.MonoidLocalization.Away` and
  `Mathlib.RingTheory.Localization.Away.Basic`: `Localization.Away`, its actual
  ring/algebra structures, `algebraMap`, and the localization universal property.
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`: `MvPolynomial`, `aeval`,
  `algHom_ext`. The actual polynomial quotient is already in the imported root views.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift`, `pullback.map`.
- `Mathlib.NumberTheory.Padics.PadicIntegers`: `PadicInt`; the existing deck group
  uses precisely these q-adic factors and their product topology.
- `Sheaf.Paper.FullParameterRootTower`: `ParameterRootDeckGroup`,
  `ParameterRootCharacters`, `parameterRootDeckInteger` (through its character
  normalization). This landed node is added to `stmt_deps`.
- `Sheaf.Paper.StrictLocalKummerTameModule`: `TameRootOrder` and `tameRootAlgebra`; the definition node `def-sfb-strict-local-kummer-tame-module` is explicitly cited.
- `Sheaf.Paper.UnitRootCoordinateTowerComparison`: `stage`, `view`, `viewMap`,
  `root`, `labels`, `labelIndex`, `labelOrder`; the actual quotient/localization
  interfaces, not private copies. The new `def-sfb-parameter-root-coordinate-views` owns these unchanged definitions and is added to `stmt_deps`; the theorem node is not a statement dependency.
- `Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech`:
  `AlgebraicGeometry.Scheme.UniversalCover.profiniteProduct`,
  `profiniteProductBase`, `profiniteProductSection`, `profiniteProductMap`.
  Its definition node `def-sfb-profinite-product-maps` is added to `stmt_deps`.
- Proof imports retain the recorded plan: `colimit`/`IsColimit` in
  `Mathlib.CategoryTheory.Limits.HasLimits`, `Spec.reflective` in
  `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`,
  `Ideal.quotientInfRingEquivPiQuotient` in
  `Mathlib.RingTheory.Ideal.Quotient.Operations`, `pullbackSpecIso` in
  `Mathlib.AlgebraicGeometry.Pullbacks`, `sigmaSpec` in
  `Mathlib.AlgebraicGeometry.Limits`, `PadicInt.toZModPow`/`PadicInt.lift` in
  `Mathlib.NumberTheory.Padics.RingHoms`, and the concrete filtered-ring-colimit
  interfaces in `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic` and
  `Mathlib.Algebra.Category.Ring.FilteredColimits`.

The downstream `FullRootRotationTorsor` has related packaging, but its proof
explicitly uses this node. It is intentionally not imported and no downstream
existence theorem is assumed. The existing algebra, character and test-object
interfaces suffice; the helper packages here only express this node's conclusions.

Edge cases checked from the definitions and source calculation: r=0 (empty product,
no root variables, all labels singleton); n=1 (ZMod 1 singleton and first-level root
relations); f=0/nilpotent f (empty punctured schemes); parameters that are zero or
zero divisors; no domain, regularity, Noetherian or locality assumption; zero rings
are not excluded by an added binder (the characteristic/primitive-root hypotheses
may themselves be unsatisfiable there); nonconstant profinite labels in the triple
identity; arbitrary compatible roots of units, including order one; ordinary base
change with u=v=1. No statement dispute found.

Searches for existing notions/statements:

- `msearch.py ... leanfinder "Cech comparison for compatible prime to p Kummer root
  towers rotation action"`: eight hits, on cyclotomic characters and field Kummer
  automorphisms; none is this general-ring simultaneous Čech theorem.
- `msearch.py ... loogle "IsPrimitiveRoot, MvPolynomial, PadicInt"`: zero hits.
- `msearch.py ... grep "Kummer|kummer|profinite.*torsor" AlgebraicGeometry`: zero hits.
- `msearch.py ... leansearch "compatible multi parameter Kummer tower Cech comparison
  prime to p"`: eight unrelated adic/localization scalar-tower hits; no match.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf`, and the algebraic-geometry part of
  Mathlib: the fixed-exponent single-parameter `ProEtale.KummerStage` is not this
  tower; the parameter root algebra, full compatible-root algebra, unit changes,
  and profinite product maps already exist and are reused. The full torsor theorem
  cites this node downstream. No `KummerCech` namespace or existing exact theorem.
- Literal node-id search in `lean/WeilConjectures` and `dag/lean_names_upstream.json`:
  no exact existing declaration. The example compact-object Sheaf module is now
  withdrawn; its node records the upstream definition, consistent with the rule
  against duplicated notions.

Validation: `scompile.py NA lem-sfb-compatible-kummer-tower-cech` compiled the
coordinate package, then the full theorem with substitution, in module mode for
both the sandbox and final library name. The final import-complete version is
checked again by the prescribed delivery dry run. No proof was attempted.

## Repair of return 6c65d72a1097

1. H2/H12, ownership: removed `lem-sfb-unit-root-coordinate-tower-comparison`
   from the added statement dependencies. Added the definition node
   `def-sfb-parameter-root-coordinate-views`, attached with `existing: true` to
   the unchanged declarations in `Sheaf.Paper.UnitRootCoordinateTowerComparison`.
   Its definition includes finite/full stages, generator labels and coordinates,
   optional boundary quotients, optional puncturing, canonical maps and inherited
   structures; it makes no assertion from the theorem. The module is not copied
   or edited. The original main-branch dependencies are preserved.
2. H3, triple isomorphism: retained the action identity `Coordinates.triple` and
   added `tripleComparison`, `tripleComparison_fst`, `tripleComparison_snd`.
   The codomain is `(X×_U X) ×_(pr₂,X,pr₁) (X×_U X)`, the specified triple
   product. The first edge is comparison(x,g); the second is comparison(gx,h).
   Thus all three vertices are fixed as scheme maps, not just point formulas.
   The fields apply at finite and full levels. Step 9 of the proof docstring now
   includes the pullback-of-double-comparisons argument and the test-object
   product identification, matching the full DAG proof.
3. H2, tame orders: added `def-sfb-strict-local-kummer-tame-module` to the item
   statement dependencies and explicitly publicly imported its module. Its
   `TameRootOrder` is used throughout; it is not defined again.
4. Second-reading attribution: the section below now identifies the actual
   independent maintainer reading and its exact findings. The worker's own
   subsequent verification is labelled as such, not described as independent.

Compared the retained node with the current read-only main-branch node: the only
changes are `lean` and the authorized added definition dependencies; there is no
change to the accepted statement or proof. The delivery wrapper rebases these
sandbox changes on its refreshed current main branch. The returned head is
6c65d72a1097; its three mathematical/ownership defects are repaired as above.

## New nodes

`def-sfb-parameter-root-coordinate-views`: an existing-declaration ownership node
for `UnitRootCoordinates.stage`, `labels`, `labelIndex`, `labelOrder`, `root`,
`boundaryIdeal`, `reduced`, `reductionMap`, `view`, `viewMap`, and their inherited
ring/coefficient instances. Source: ILO IX 2.1 p.133 root presentation and the
explicit boundary/localization calculation of the existing unit-coordinate node.
The statement spells out the definitions at all optional-order, optional-boundary
and puncturing settings, including boundary tags 0 (roots), 1 (coefficients),
2 (product). It states only real constructions. LeanSearch and LeanFinder found
related general localization/quotient or standard-etale declarations but no exact
combined interface; Mathlib/upstream RingTheory grep found no such interface.
The Sheaf search finds these exact declarations at lines 40–155 in the unchanged
published module, hence `existing: true` and no new Lean file. The DAG search
finds only their original theorem-node attachment, and no definition owner;
`blueprint_refs.py search` found no corresponding blueprint unit. The new node
owns the definitions as explicitly requested by the maintainer. Its `from.node`
is null, exactly as `blueprint_refs.py ancestor` reports for this item; its via
chain prepends the current item. The searches are recorded with their actual
service outputs in `mathlib_searches`.

## Second reading by NA

Independent reading: maintainer L's immutable-head review of
6c65d72a1097, recorded in `coord/returns/NA.md` on 2026-10-24 at 08:00 UTC.
L checked the exact hypotheses, quotient/localization objects, scheme limit,
rotations, fixed comparisons, residue normalization and uniqueness, substitution
orientation/naturality, empty cases, docstrings and verbatim signature. L found
that the root-view definitions needed their own definition node, the triple
identity did not yet include its isomorphism, and `TameRootOrder` needed its
owning dependency. The repairs above address each finding. This attribution
replaces the previous misleading placement of a self-check under this heading.

Repair verification by the worker (not an additional independent review): read
both the amended module and the new definition-node statement. Checked all three
triple vertices via the two edge equations, the h*g multiplication order, and
the base of the iterated pullback. Matched all fourteen attached existing plain
declarations to the new node, including each boundary tag and each instance.
Checked r=0, n=1, empty punctures and zero coefficient rings as before. The
maintainer's independent review of the repaired head remains the normal delivery
review; no unperformed independent reading is claimed. The dispatcher still
prohibits spawning other agents.
