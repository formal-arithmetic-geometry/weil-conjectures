## Worker report

The module `Sheaf.AlgebraicGeometry.ReducedCurveTorsionfreeBiduality` states
`AlgebraicGeometry.reducedCurve_torsionfree_biduality`, with its whole proof `sorry`.
No definitions, hypotheses, DAG dependencies or node statement were changed.
There are no new nodes or dependency modules.

The statement was read against Stacks `dualizing.tex`, Tag 0B5A,
`lemma-local-CM`, final assertion and proof (lines 3090ff in the local source).
That proof gives the canonical CM duality through derived biduality. The supplied
node spells out its sheaf form using the representing dualizing module on a
proper reduced pure-dimensional-one curve. The latest blueprint's
`sec-six-functors-basics/sk-thm-sf-ctf-stability/` direct-images proof was read;
it currently uses compactification and does not expand this historical
alteration prerequisite. The node and its accepted stage-1 route are preserved.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A field k is `(k : Type u) [Field k]`.
- A k-scheme is `(C : Scheme.{u}) [C.Over (Spec (.of k))]`.
- Nonempty, proper and reduced are `[Nonempty C]`,
  `[IsProper (C ↘ Spec (.of k))]`, and `[IsReduced C]`.
- Pure dimension one is `hPure : C.IsPureDimension 1`; its actual definition
  quantifies over irreducible components and their subspace Krull dimensions.
- The chosen dualizing module together with its natural representing linear
  bijections is `D : ReducedCurveDualizingPair k C`. Its `omega`, `coherent`,
  `duality` and `naturality` fields supply precisely the chosen pair, without
  choosing an arbitrary coherent module or assuming extra local properties.
- The coherent O_C-module is `(F : C.Modules)` with
  `hF : RingedSpace.IsCoherent C.toRingedSpace F`. This is the finite-type and
  finite-type-kernel condition of Tag 01BV, rather than a substitute notion.
- The hypothesis `hDetect` quantifies over every open U and every section s.
  For every `Z ∈ irreducibleComponents C`, every generic point eta of Z and
  every `hη : η ∈ U`, its antecedent says
  `TopCat.Presheaf.germ F.val.presheaf U η hη s = 0`; its consequent is `s = 0`.
  This uses germs in the recorded stalk carriers; it is not merely an assertion
  about global sections, or about nonzero stalks being torsion-free over domains.
- F dagger is everywhere the existing
  `SheafOfModules.homObj (R := C.sheaf) F D.omega`; the explicit ring-sheaf
  argument is needed for elaboration and introduces no second Hom construction.
- The first conclusion is `RingedSpace.IsCoherent` for that very Hom sheaf.
- The second conclusion repeats the identical all-open generic-germ detection
  condition for the Hom sheaf, including opens without any component point.
- The final conclusion supplies a morphism delta from F into its twice-iterated
  sheaf Hom with D.omega. For every U, s, V, inclusion `i : V ⟶ U`, and local
  morphism phi over V, its value satisfies
  `(((δ.val.app (op U)) s).app (op (Over.mk i))) φ =
    (φ.app (op (Over.mk (𝟙 V)))) (F.val.map i.op s)`.
  The left side evaluates delta(s), viewed as a morphism on the localized site,
  on V and phi. The right side applies phi on V to the restriction of s.
  In particular V = U, i = identity is exactly delta(s)(phi) = phi(s).
  Quantification over every smaller open also specifies the entire Hom section.
- `IsIso δ` asserts invertibility of that same evaluation morphism.
- The final `∀ δ', (all-open evaluation formula) → δ' = δ` states uniqueness
  among *all* module morphisms with the formula, without assuming delta prime
  is invertible. This is existence and uniqueness of the canonical map, not a
  hypothesis of an arbitrary bidual isomorphism. No construction is chosen from
  a mere nonunique existence assertion and no definition contains sorry.
- No local freeness, generic-rank constraint, connectedness, nodal assumption,
  Gorenstein assumption or nonzero-F condition occurs in the binders.

Dependency declarations used (their full signatures and docstrings were read):

- `Mathlib.Algebra.Field.Defs`: `Field` (through the recorded module imports).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Sheaf.AlgebraicGeometry.PureDimension`:
  `AlgebraicGeometry.Scheme.IsPureDimension`.
- `Sheaf.AlgebraicGeometry.ReducedCurveDualizingModule`:
  `AlgebraicGeometry.ReducedCurveDualizingPair`, including its four fields,
  and the existence/uniqueness theorem `exists_reducedCurveDualizingPair`.
  The theorem takes an arbitrary chosen representing pair, as the node requests.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly exposes the exact
  `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `WeilConjectures.AlgebraicGeometry.Coherent`, as its repaired dependency record
  explicitly specifies. Its separate `IsQuasiCoherentFiniteType` predicate is
  not mistaken for coherence.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, with
  `IsGenericPoint` from `Mathlib.Topology.Sober`.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor` and the module-stalk
  dependency's documented sheaf specialization give the stalk/germ convention.
  The formula uses Mathlib `TopCat.Presheaf.germ` on `F.val.presheaf`, exactly
  the carrier of `RingedSpace.moduleStalkFunctor` on these sheaves.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`; its underlying
  `PresheafOfModules.homObj` has sections given by morphisms of restrictions
  to `Over U`. This is why the two `.app` operations in evaluation are genuine
  local module morphism evaluations, including the correct restriction of s.

All recorded project modules for stated proof dependencies are plain imports;
Mathlib leaf proof dependencies are also imported from their recorded modules.
The proof docstring follows all fourteen proof steps, including the zero-stalk
case and the canonical-evaluation normalization. Three proof-only nodes have
no recorded Lean declaration yet and contribute no import:
`lem-sfb-proper-field-algebraic-dualizing`,
`lem-sfb-normalized-cm-local-dualizing-concentration`, and
`lem-trf-finite-module-canonical-biduality`.
They are proof prerequisites only, not missing notions in this statement.

Edge cases checked before writing:

- F = 0 is permitted. Its dual is zero and the unique evaluation is the zero
  object's identity isomorphism; generic detection is valid.
- U = empty is included; the sheaf condition gives only its zero section.
- A coherent module supported at a closed point with nonzero stalk fails
  hDetect: all generic stalks vanish, so it is correctly excluded.
- F can have rank zero on some components and different ranks on others.
- Reducible/disconnected curves and non-Gorenstein singular curves are allowed;
  omega is not assumed invertible and F is not assumed locally free.
- All generic points lying in U are tested; hDetect does not silently ignore
  components, restrict to closed points, or quantify only over affine opens.
- The empty curve is explicitly excluded by the node, and so by `[Nonempty C]`.
- Arbitrary characteristic and arbitrary object universe u are retained, using
  the same field/scheme size convention as the recorded representing pair.

Searches for an existing declaration:

1. `msearch.py ... leanfinder`, query
   "canonical evaluation biduality coherent torsion free sheaf on reduced curve
   dualizing module": 8 hits, all unrelated scheme/residue-field evaluation or
   smooth-sheaf evaluation, no theorem of this statement.
2. `msearch.py ... loogle`, query `SheafOfModules.homObj`: no hits, identifier
   unknown to the Mathlib-only search index. The project declaration was then
   opened directly and used.
3. `msearch.py ... grep`, query `bidual|Bidual|homObj`, subdirectory
   `Algebra/Category/ModuleCat`: no Mathlib hits.
4. `msearch.py ... leansearch`, query "Coherent torsion free modules over reduced
   curves are isomorphic to their double dual with respect to a dualizing
   module": 8 hits on ordinary ring-valued module duals/reflexivity and
   fractional ideals, none stating this coherent curve theorem.
5. `rg` on `lean/WeilConjectures` and `lean/Sheaf` for biduality, generic-section
   detection, torsionfree, and the item id. Existing
   `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Bidual` was opened:
   `SheafOfModules.bidual` targets the unit sheaf and `isIso_bidual` assumes
   finite local freeness. They do not state omega-valued biduality for coherent
   modules with generic-section detection. Other hits are derived/etale
   biduality, abelian-variety biduality or unrelated module statements.
   No matching declaration or duplicate name was found.

Validation: the initial scompile diagnosed failure to infer the ring-sheaf
parameter of homObj. Every occurrence was repaired with `(R := C.sheaf)`.
The resulting file passes both the sandbox and actual-module checks of
`scompile.py` without errors or unexpected warnings. The only postponed proof
is `AlgebraicGeometry.reducedCurve_torsionfree_biduality`.
There is no STATEMENT-DISPUTED flag and no statement correction.

## Second reading by NI

Author's second reading, as required for this direct-delivery dispatcher;
the maintainer provides the independent review. Reopened the node and final
Lean signature side by side. Checked all field, scheme, properness, reducedness,
purity and nonempty binders; checked D is the actual natural representing
pair and hF is Tag 01BV coherence. Checked the antecedent and conclusion of
hDetect on all opens, then the same condition on the exact Hom sheaf. Checked
that the evaluation formula has phi defined over V and restricts s from U to V,
and that the uniqueness comparison makes no IsIso assumption on delta prime.
Checked invertibility applies to the same witness delta. No mathematical
mismatch was found. The only elaboration repair was making the existing Hom
construction's structure-sheaf argument explicit. No axiom or proof was added,
no data definition introduced, and no node field outside lean was changed.
