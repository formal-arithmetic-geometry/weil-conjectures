## Worker report

The module `Sheaf.AlgebraicGeometry.TorsionSheafCharacterizations` states two named theorems,
`AlgebraicGeometry.Scheme.isTorsionAbelianSheaf_characterizations` and
`AlgebraicGeometry.Scheme.constant_ratModIntSheaf_sections_not_torsion`. Both proofs are `sorry`.
No definition, new node, dependency module, or statement correction is needed.

Hypothesis and clause correspondence:

- Scheme T: `{T : Scheme.{u}}` in the characterization and `(T : Scheme.{u})` in the example.
- Abelian sheaf F on the small étale site: `Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`.
- Condition (1), the canonical colimit map is an isomorphism: the existing
  `Scheme.IsTorsionAbelianSheaf F` from `Sheaf.AlgebraicGeometry.TorsionEtaleSheaf`.
  I read its full definition, including the positive-divisibility index, kernel transitions,
  cocone of kernel inclusions, and `IsIso (colimit.desc D c)`.
- Condition (2): `∀ (U : T.Etale) (s : F.obj.obj (op U)), ∃ R : Sieve U,
  R ∈ T.smallEtaleTopology U ∧ ∀ (V : T.Etale) (f : V ⟶ U), R f →
  ∃ n : ℕ, 0 < n ∧ n • F.obj.map f.op s = 0`. A covering sieve is precisely a covering
  family with its refinements. Given the node's family, its generated sieve satisfies this:
  each refinement inherits the integer on a generating arrow. Conversely a covering sieve
  contains a jointly surjective étale covering family, and its arrows have the stated
  annihilators. Morphisms between étale T-schemes are themselves étale. No uniform integer
  or finiteness condition is imposed.
- Condition (3): quantify over `Ω : Type u`, `[Field Ω]`, `[IsAlgClosed Ω]`, and
  `t : Spec (.of Ω) ⟶ T`; the group is
  `((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F`.
  Torsion is written elementwise, `∀ x, ∃ n : ℕ, 0 < n ∧ n • x = 0`.
  This uses the recorded geometric-point and stalk declarations, in their pinned universe.
- Equivalence of the three conditions is `(1 ↔ 2) ∧ (1 ↔ 3)`.
- The constant Q/Z sheaf: G has the same abelian-sheaf type and `hG` identifies it exactly
  with `(constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
  (AddCommGrpCat.of (ULift.{u + 1} (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ))))`.
  The subgroup of integer multiples of 1 is the embedded Z, so this is Q/Z.
  ULift is an additive universe lift, with no change to the group. The G/hG binders merely
  name this expression: substitution gives the theorem directly for the specified constant
  sheaf; it does not assume any extra mathematical condition on T or the constant sheaf.
- This G is torsion: `IsTorsionAbelianSheaf G` is an unconditional conjunct, including empty T.
- Nonempty T: `Nonempty T → ...` guards only the infinite-order example.
- The étale T-scheme U is `U : T.Etale`; `e : U.left ≅ ∐ (fun _ : ℕ+ ↦ T)` identifies its
  underlying scheme with the specified coproduct. The equation
  `U.hom = e.hom ≫ Sigma.desc (fun _ : ℕ+ ↦ 𝟙 T)` specifies its codiagonal structure map.
- Coprojections: `j : ∀ n : ℕ+, Etale.mk (𝟙 T) ⟶ U` with
  `(j n).left = Sigma.ι (fun _ : ℕ+ ↦ T) n ≫ e.inv`.
- The canonical restriction group isomorphism is expressed as bijectivity of the actual
  restriction map `fun s ↦ fun n ↦ G.obj.map (j n).op s`. Each coordinate is an additive
  homomorphism, so bijectivity is exactly the group-isomorphism claim, without choosing an
  unrelated isomorphism. Function types express the unrestricted product.
- The specified section: `∃ x : G.obj.obj (op U)` whose n-th restriction is the component of
  `toSheafify` of the constant presheaf at `Etale.mk (𝟙 T)`, applied to the quotient class of
  `1 / (2 : ℚ) ^ (n : ℕ)`, lifted by ULift. `hG.symm ▸` transports that section along the
  equality naming G. Thus it is exactly the node's `ι_T(1/2^n)`, not an arbitrary example.
- Infinite order: `∀ k : ℕ, 0 < k → k • x ≠ 0`. In particular the section group is not torsion.

Dependencies read and used: `CategoryTheory.Sheaf` (Mathlib.CategoryTheory.Sites.Sheaf);
`AlgebraicGeometry.Scheme.smallEtaleTopology` and `Scheme.Etale`
(Mathlib.AlgebraicGeometry.Sites.Etale, with the latter's constructor in Morphisms.Etale);
`Scheme.IsTorsionAbelianSheaf` (Sheaf.AlgebraicGeometry.TorsionEtaleSheaf);
`Scheme.SpecToEquivOfField` / `IsAlgClosed` (Mathlib.AlgebraicGeometry.ResidueField,
used in the recorded specialization as an algebraically closed field and Spec morphism);
`GrothendieckTopology.Point.sheafFiber` (Mathlib.CategoryTheory.Sites.Point.Basic) and
`Scheme.pointSmallEtale` (Mathlib.AlgebraicGeometry.Sites.EtalePoint);
`CategoryTheory.constantSheaf` (Mathlib.CategoryTheory.Sites.ConstantSheaf).
The example's canonical map is Mathlib `CategoryTheory.toSheafify`, not a private copy.
I read these declarations' docstrings/signatures and the supporting étale constructor.

Sources read on the server (the local clone holds literature lists, not source texts):
`literature/blueprint/master/blueprint/sec-proper-base-change/sk-def-pbc/_section.md`
and `literature/blueprint/master/blueprint/sec-abelian-varieties/`
`sk-prop-av-finite-etale-points/def-weil-pbc-etale-sheaves.md`.
The former explicitly states all three characterizations; the latter gives the Q/Z example.

Edge cases: zero sheaf satisfies all three conditions; over the empty scheme the empty
cover handles any section and no geometric point exists. The example asserts constant-sheaf
 torsion also for empty T, but requires nonemptiness for infinite order. Empty covering
families are allowed; positive integers exclude 0 as a vacuous annihilator. ℕ+ starts at 1,
matching the example. The infinite coproduct is not restricted to a finite or connected T.
The étale category includes non-quasi-compact U. All universe and variable binders are explicit.
There are no private definitions, local notation, or added structural hypotheses.

Searches (2026-10-11):

- `msearch.py ... leanfinder "An abelian etale sheaf is torsion if and only if all geometric
  stalks are torsion and sections are locally annihilated by positive integers"`: eight
  unrelated stalk/smoothness/module results; no characterization.
- `msearch.py ... loogle "IsAddTorsion, sheafFiber"`: zero hits, unknown identifier sheafFiber.
- `msearch.py ... grep "IsAddTorsion|torsion" CategoryTheory/Sites`: zero Mathlib hits.
- `msearch.py ... leansearch "torsion abelian sheaf equivalent locally killed by positive
  integers geometric stalks torsion"`: service unavailable (Internal Server Error).
- `rg` over upstream WeilConjectures for the item id: no hits. Concept searches found
  `AlgebraicGeometry/Sites/TorsionSheaf.lean` and the existing module-sheaf torsion predicates;
  these give bounded annihilation/pullback and other encodings, not the colimit characterization
  and full specified Q/Z counterexample. They are not substitutes for this node.
- `rg` over `lean/Sheaf/AlgebraicGeometry` for `IsAddTorsion`, torsion iff, and locally killed:
  no matching statement. The existing `TorsionEtaleSheaf.lean` defines condition (1), reused.
- `rg` over `dag/lean_names_upstream.json`, Mathlib and WeilConjectures for the selected
  declaration names: no collision. Mathlib quotient and sheafification declarations provide
  the example's group and its canonical map directly.

Validation: server single-file compile clean (2.1 seconds); delivery dry run is the final check.
No STATEMENT-DISPUTED issue or node fault found.

## Second reading by P1

Independent reading of the node copy, both delivered theorem signatures, all six
statement-dependency nodes, and the declarations realizing those dependencies. No
mathematical mismatch found; the Lean and node signature are left unchanged. This
section and the independent search log are the only additions by the second reader.

I read the source texts over ssh on the server: the unit sk-def-pbc/_section.md,
sec-abelian-varieties/sk-prop-av-finite-etale-points/def-weil-pbc-etale-sheaves.md,
and etale-cohomology.tex at Definition 040R (definition-stalk), Lemmas 03PR and
03PT, Theorem 03PU, and Section 0DDB. The characterization concerns arbitrary
schemes. The quasi-compact/quasi-separated assumptions in 0DDB concern the
subsequent cohomology theorem, not the torsion definition or stalk criterion.
The unit's properness assumption is on the morphism in the PBC property, not on
T in this subsidiary characterization. No source-wide hypothesis is missing.

Object, hypothesis, and conclusion checklist (all verdicts PASS):

| Node item | Lean rendering and verdict |
| --- | --- |
| Arbitrary scheme T | `{T : Scheme.{u}}` / `(T : Scheme.{u})`; no extra geometric assumptions. |
| Abelian sheaf F on the small etale site | `Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`; exactly the recorded dependency encoding. |
| (1) canonical colimit map is an isomorphism | `IsTorsionAbelianSheaf F`; I opened TorsionEtaleSheaf.lean: positive integers with divisibility, kernels `kernel (n.val • 𝟙 F)`, kernel inclusions, their cocone, and `IsIso (colimit.desc D c)`. |
| (2) each section locally killed by positive integers | `∀ U s, ∃ R : Sieve U, R ∈ T.smallEtaleTopology U ∧ ∀ V f, R f → ∃ n : ℕ, 0 < n ∧ n • F.obj.map f.op s = 0`; order of quantifiers allows both cover and integers to depend on s, and integers to vary by arrow. |
| Covering family, arbitrary size | A covering sieve contains a jointly surjective etale covering family. A family's generated sieve includes refinements; an annihilator remains valid after restriction. Thus the sieve formulation is equivalent, including empty covers. |
| (3) each geometric stalk a torsion group | `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T), ∀ x, ∃ n, 0 < n ∧ n • x = 0`, with x in `(pointSmallEtale t).sheafFiber.obj F`. |
| Equivalence of all three conditions | `(1 ↔ 2) ∧ (1 ↔ 3)`; neither implication nor criterion omitted. |
| Constant Q/Z sheaf | G with `hG` identifying it with `constantSheaf ...` of `AddCommGrpCat.of (ULift (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)))`; the subgroup is exactly Z. Substitution eliminates G/hG, so these are naming binders, not an added restriction. |
| This sheaf is torsion | `IsTorsionAbelianSheaf G`, unconditionally. The empty-scheme case is true as well. |
| T nonempty for the counterexample | `Nonempty T → ...`, guarding only the infinite-order example. |
| U is the etale coproduct of copies indexed by n >= 1 | `∃ U : T.Etale, ∃ e : U.left ≅ ∐ (fun _ : ℕ+ ↦ T), ...`; positive naturals start at 1. |
| Structure morphism is the codiagonal | `U.hom = e.hom ≫ Sigma.desc (fun _ : ℕ+ ↦ 𝟙 T)`. |
| Coprojections in the site | `j : ∀ n : ℕ+, Etale.mk (𝟙 T) ⟶ U` with `(j n).left = Sigma.ι ... n ≫ e.inv`; the over-category morphisms retain compatibility with T. |
| Canonical restriction group isomorphism to the product | `Function.Bijective (fun s ↦ fun n ↦ G.obj.map (j n).op s)`; this is the actual additive restriction map. Bijectivity of this homomorphism is precisely the group-isomorphism claim. |
| Specified section, rather than an arbitrary infinite-order element | `∃ x`, each restriction equal to the `toSheafify` component at `op (Etale.mk (𝟙 T))` applied to the lifted quotient class of `1 / (2 : ℚ) ^ (n : ℕ)`; `hG.symm ▸` transports it into G(T). |
| Infinite order, hence sections not a torsion group | `∀ k : ℕ, 0 < k → k • x ≠ 0`; this supplies the precise counterexample. |

Dependency declarations checked in their source modules: `CategoryTheory.Sheaf`
is the full subcategory of sheaf presheaves; `Scheme.Etale` is the category of
etale T-schemes and its arrows are themselves etale; the topology and
`ofArrows_mem_smallEtaleTopology_iff` give jointly surjective coverings.
`SpecToEquivOfField` identifies Spec-field maps with residue-field embeddings.
`pointSmallEtale` uses the lift functor, and `Point.presheafFiber` is its
opposite category-of-elements colimit; `sheafFiber` composes with the underlying
presheaf functor. This is precisely the node's pointed-neighbourhood stalk.
`constantSheaf` is constant-presheaf followed by sheafification, and
`toSheafify` is the actual sheafification unit. All notions are reused. There
are no new definition nodes or dependency modules to review, and no statement
correction or citer verdicts to recheck.

Edge cases checked: the zero sheaf satisfies all three conditions. On an empty
scheme every etale object is empty, the empty cover witnesses (2), and (3) is
vacuous; no nonempty hypothesis appears in the characterization. The constant
sheaf torsion assertion remains valid there, while the example is guarded.
Neither a finite index set nor a quasi-compact U is required. The countably
infinite coproduct is permitted. An annihilator n = 0 is excluded by `0 < n`;
no characteristic restriction is imposed, and coefficient Q/Z is an additive
group independent of the base characteristic. `u` is explicitly bound. The
scheme, etale objects and geometric-point fields use the same universe, as in
the recorded declarations; algebraic closures of residue fields exist there,
so the tests are not vacuous. The abelian value universe u+1 is the established
site encoding, and ULift preserves the group and its order properties.

Independent searches used other wording than the first reader:

- LeanFinder via msearch: `geometric fibers detect torsion of an abelian sheaf;
  locally finite additive order` returned module finite-type results and
  `Module.finite_of_fg_torsion`, not this statement.
- Loogle via msearch: `AddMonoid.IsTorsion` returned the group-level alias of
  `IsAddTorsion`, not a sheaf theorem.
- LeanSearch via msearch: `constant rational modulo integer sheaf infinite order
  sections on countable disjoint union` was unavailable (Internal Server Error);
  no negative mathematical verdict is inferred from that failure.
- Independent rg searches over Mathlib sites, WeilConjectures, and lean/Sheaf
  for local annihilation, finite additive order, torsion equivalences, Q/Z,
  `ratModIntSheaf`, and the chosen declaration names found no exact full-node
  statement or declaration-name collision.
- I followed the upstream hits to EtaleTorsion.lean, Sites/Point/Torsion.lean,
  SheafCohomology/Basic.lean, and BaseChangeTheorems/TorsionSheaf.lean.
  `Scheme.isTorsion_iff_isAddTorsion_sheafFiber` starts from the local-section
  predicate `Sheaf.IsTorsion` and tests separably closed fields; it does not
  identify the canonical colimit predicate used by this node. The module-sheaf
  `IsTorsionSheaf.exists_isColimit` only supplies some bounded diagram, not this
  canonical map. Neither includes the specified Q/Z coproduct counterexample.
  These are useful proof ingredients, not an existing realization of this node.

H5/H6/H8/H9 checks: no definitions in the delivery, exactly two named theorems
with sorry proofs, no private aliases/local notation/local instances, all
variables bound, and both docstrings give their source and blueprint id.
Their proof explanations jointly cover steps 1-7 of the node. No repair was
needed and no correct code was rewritten. Single-file server compilation and
both delivery checks are run after this reading.
