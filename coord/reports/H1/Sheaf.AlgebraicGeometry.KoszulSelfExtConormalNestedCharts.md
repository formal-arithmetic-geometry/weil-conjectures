## What changed

Proved the body of
`AlgebraicGeometry.koszulRegularImmersion_self_ext_conormal_nested_charts` in
`Sheaf.AlgebraicGeometry.KoszulSelfExtConormalNestedCharts`, without changing its signature,
universes, hypotheses or visibility. Updated its proof docstring and node proof to match the
implemented route. Added proof-only imports of `SelfTorConormalDualChart` and
`SelfExtTorDualChart`; the original public imports are unchanged.

The intermediate object is the actual self-Tor sheaf
`i*H^{-n}(B[0] tensor^L B[0])`, using `schemeDerivedTensorMonoidal`. A global
exterior-to-Tor morphism and a global Ext-to-dual-Tor morphism yield, after dualizing the
former, one global morphism from T to F. Both are invertible on each regular chart. Their
composite is therefore invertible there. The comparison family consists of its inverses.

The two private helpers are fully proved. `over_comp_isIso` expresses preservation of
composition by the over functor. `compatible_inverse_family` evaluates inverse identities
on an arbitrary common subopen and proves equality by associativity. This proves the
required nested compatibility without choosing matrices or performing a second resolution
comparison. The inverse-family helper actually works without a nesting hypothesis.

Added two new statement modules, each with one public theorem and a matching DAG node.
They are independent parts: the first mentions exterior conormal and Tor, but no Ext;
the second mentions Ext and Tor, but no exterior conormal or chart compatibility.
Neither asserts the original conclusion under another name. No existing definition,
statement interface, target, unit record or module held by another group is adapted.

Single-file compilation succeeded for all three modules, including the complete assembly
and inverse-compatibility proof. The composition helper avoids unnecessary expansion of
the derived tensor implementation during elaboration.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.koszulRegularImmersion_self_ext_conormal_nested_charts`
(node `new-s3-koszul-conormal-nested-charts`). Its module contains no remaining `sorry`.

Added exactly two holes, each in a new module with body `:= by sorry`:

- `AlgebraicGeometry.selfTor_conormal_dual_chart`, in
  `Sheaf.AlgebraicGeometry.SelfTorConormalDualChart`, node
  `lem-sc-self-tor-conormal-dual-chart`.
- `AlgebraicGeometry.selfExt_tor_dual_chart`, in
  `Sheaf.AlgebraicGeometry.SelfExtTorDualChart`, node
  `lem-sc-self-ext-tor-dual-chart`.

This is a decomposition, not an axiom-free proof of the original mathematics: one original
hole is closed by combining two strictly smaller comparison statements. The delivered
source-file hole balance is 1 closed minus 2 added, namely -1. This is not a measured
closure-ledger improvement. In particular the derived tensor construction also brings its
existing dependencies into the import closure. The maintainer's pinned ledger decides
closure counts and pruning. No data definition chooses a witness of an unproved existence
theorem, and there is no `sorry` in a definition or private helper.

The two new statements have no global regularity, Noetherian, positive-generator-length,
proper-ideal or derived-category-on-Z assumptions. Their isomorphism assertions apply only
to supplied regular affine charts. Edge checks: n=0 is quotient multiplication; n above
the generator length gives zero modules; m=0 is the zero ideal; the zero quotient and empty
inverse-image charts give zero sheaves. The exterior-to-Tor construction uses odd-square
vanishing from strictly commutative dg algebra resolutions, not merely the sign rule,
so characteristic two is included.

## No longer needed

No original public import was removed; the item's statement interface is preserved. There
were no original proof-only imports. In the new statement modules the unused explicit
imports of `DerivedCategory` and `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`
were removed before delivery; `SelfTorConormalDualChart` does not explicitly import
`DerivedInternalHom`, and `SelfExtTorDualChart` does not import `Modules.ExteriorSheaf`.

The original eight direct node proof dependencies are replaced by the two new comparisons.
Six remain below the new comparisons, rather than being pruned:
`lem-sc-affine-conormal-frame`, `lem-sc-affine-quotient-resolution-sheafification`,
`lem-sc-derived-hom-finite-free-model`, `lem-sc-derived-internal-hom-restrict-open`,
`lem-sc-koszul-conormal-basis`, and `new-j3-koszul-projective-resolution`.

The new route does not need these two original dependencies:

- `lem-sc-koszul-regular-flat-base-change`, module
  `Sheaf.RingTheory.KoszulRegularFlatBaseChange`.
- `new-q2-koszul-generator-chain-map`, module
  `Sheaf.RingTheory.KoszulGeneratorChainMap`.

Regularity is already supplied separately on each chart. The global Tor constructions,
followed by uniqueness of inverses, replace generator substitutions and restrictions of
one chart's Koszul-regular sequence to another. This is route-level pruning; no claim is
made that another target does not independently reach those modules.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the original statement was found. Its planned generator-change
argument is unnecessary once the two canonical comparisons through self Tor are available.
The original conormal-basis and finite-free resolution lemmas alone do not construct a
single global normalized map; the two new statements expose precisely the missing parts.

The blueprint ancestry helper reports `None` for this item's module and node id, because
its `created.item` fields contain module names rather than DAG ids. The existing explicit
`blueprint.from` links do trace the item through local comparison to the imported node
`lem-sc-finite-duality`. The new nodes record that ancestor and the entire intervening
chain, without changing existing ancestry fields. Whole-blueprint searches for Koszul Tor,
Ext Tor, conormal Tor, exterior Tor, self-Tor and Tor_n found no matching blueprint node.
No unit-level statement or realized proof step is bypassed or changed.

A direct assembly initially timed out when elaboration expanded the derived tensor model.
Expressing the composition of restricted maps through the proved `over_comp_isIso` helper
resolved this. An experimental local irreducibility attribute was removed when preflight
classified it as an interface change. There is no time-limit increase or changed shared
definition.

## New nodes

`lem-sc-self-tor-conormal-dual-chart` is the global exterior-to-self-Tor comparison,
with chartwise invertible dual. Sources: Stacks 09PQ (Tate dg algebra and strictly
commutative Tor), 062I (conormal basis), 0BQY (Koszul resolution) and 06YH (derived tensor).
Its proof describes the Tor_1 boundary, alternating multiplication, localization and
sheafification, followed by the regular-chart wedge computation and dualization.

`lem-sc-self-ext-tor-dual-chart` is the global cap pairing from self Ext to dual
self Tor, invertible on regular affine charts. Sources: Stacks 0BQY, 08DH and 068G.
Its proof describes cap evaluation of derived Ext classes on Tor classes, descent of
quotient scalars and internal currying, then perfect finite-free Koszul evaluation.

Both nodes include three kinds of Mathlib search; LeanSearch was unavailable and is
explicitly recorded as such. Neither Loogle/LeanFinder nor regex searches supplied these
comparisons. The Stacks source files used for the proof descriptions were read during
work and cached under the sandbox scratchpad. No change record is needed: no existing
statement, definition or public import was changed.

## Second reading by H1

1. **Interface: PASS.** Read the full diff against the repository module. The sole
   existing theorem's signature, including both universes, the supplied derived-category
   instance, closed-immersion instance, arbitrary V, n, chart hypotheses and component
   equality, is byte-for-byte identical. All original public imports and visibility stay.
   The additions are two private proved helpers and two plain proof imports. There are no
   adapted existing modules, changed definitions or change records. The existing node's
   only changed fields are proof, proof_deps and proof_origin.

2. **Proof and axioms: PASS as a decomposition.** Compiled all three delivered modules
   through lcompile.py in import order without errors or warnings (4.7 s, 3.7 s and
   14.7 s). A scratch copy with explicit #print axioms compiled in 43.6 s. Both helpers
   use only propext, Classical.choice and Quot.sound. The assembled theorem and the two
   split comparisons use those plus sorryAx, as reported. The two new public theorems
   are the only direct sorry bodies; there are no data definitions, private holes or
   forbidden declarations. Checked the inverse identities componentwise: gj followed
   by f is identity on F, and f followed by gk is identity on T, so the associativity
   calculation has the correct direction. Witness extraction is inside a proposition
   proof; it supplies no public data definition from an arbitrary existence witness.

3. **Split statements: PASS.** Read both complete docstrings and nodes against Stacks
   09PQ (dpa.tex, lemma-divided-powers-on-tor), 062I
   (more-algebra.tex, lemma-H1-regular-quasi-regular), 0BQY
   (duality.tex, lemma-regular-ideal-ext), 08DH (derived internal Hom, restriction and
   tensor-Hom adjunction), and 068G (equation-simple-tor-product). The first comparison
   constructs conormal exterior -> actual self-Tor, with no Ext term; the second
   constructs self-Ext -> dual self-Tor, with no conormal term. Neither restates the
   chart-isomorphism family or its compatibility. The Tor boundary is Tor_1(B,B)=I/I²;
   multiplication is alternating because odd squares vanish, including characteristic
   two. The cap evaluation on Hom(P,B) and P tensor B descends through boundaries;
   quotient scalars allow its pullback to Z. On a Koszul-regular chart these complexes
   have zero differential, and finite wedge evaluation is perfect. This uses neither
   Noetherianity nor properness of the ideal. Checked n=0 (unit/evaluation), m=0 and
   I=0 (only degree zero), n>m (zero terms), I=A (empty inverse image), empty V, and
   the regular example A=F_2[x], I=(x) (no division by 2). The global morphisms can be
   defined on singular charts; invertibility is asserted only on regular charts.
   Independent LeanFinder queries used derived Hom/tensor pairing and alternating
   multiplication language; they returned general projective-resolution Ext tools and
   ModuleCat.exteriorPower.desc, not either comparison. Loogle's broad Tor-name query
   gave irrelevant substring hits and establishes no absence. Direct rg on Mathlib's
   Algebra, CategoryTheory and RingTheory and on both project/source libraries found
   no cap-product or conormal/Tor comparison. No short existing proof closes either
   substantial construction, so both named holes remain.

4. **Route, imports and pruning: PASS.** The assembly follows the two comparison
   maps by functorial composition and proves compatibility by uniqueness of inverses;
   it does not repeat local resolution comparisons. The two added imports are plain
   imports used only by the proof. The new statement modules publicly import the
   definitions and derived tensor instance that their signatures require. The eight
   old direct proof dependencies are all accounted for under No longer needed:
   six remain in the new comparison plans, while flat regular base change and
   generator chain maps are unused. This is pruning of the old proof route, not a
   claim of removal from the entire target closure. Read sk-thm-picard-duality.json:
   realized.statement and its sole realized step are empty, and no unit record changes.
   The item remains in the finite-duality branch; no realized unit step is bypassed.

5. **DAG agreement: PASS.** Compared each node's lean.statement verbatim with its
   declaration signature and checked proof_deps equals the union of proof-step uses.
   The existing node describes the actual restricted composition, subtype of regular
   charts and component inverse proof. The new nodes have sources, complete proof
   plans, statement dependencies, search records, split status, creation record,
   chapter/unit and blueprint ancestry, and the correct new module/declaration paths.
   Read the seven distinct older dependency statements: the conormal sections/frame,
   conormal basis, Koszul projective resolution, sheafified augmentation, finite-free
   derived Hom model and open restriction provide exactly the local calculations
   claimed in the plans. The remaining global Tor algebra and cap constructions are
   explicit tasks in the new holes, not asserted to follow from a frame alone.

**Second-reading changes:** added this independent review and its verification/search
results. No Lean proof, signature, import, node or hole count required repair. One original
hole is closed and two strictly smaller holes are added; this remains a decomposition,
not an axiom-free proof or a claimed positive ledger balance.
