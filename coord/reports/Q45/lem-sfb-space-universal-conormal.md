## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceUniversalConormal` states the node in five
sorry-only theorems. Its seven helper definitions are presentations of the notions
and canonical maps introduced in this node, with real data and no new axiom.
The statement is unchanged. The H2 repair adds two definition-node owners of
already landed declarations; no dependency module is changed.

Hypothesis and clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; every space is `AlgebraicSpace S`. All
  scheme tests, chart schemes, and coefficient rings retain universe u; the
  common-topos sheaves have universe u+1. The site's objects can have universe u+1.
- First-order thickening means the landed `IsSpaceFirstOrderThickening`, defined
  by `IsRepresentableWith` and the existing scheme `IsFirstOrderThickening`.
  This tests every scheme base change, with closed immersion and square-zero ideal.
- `SpaceFormallyUnramified h` expresses exactly injectivity of restriction on
  Hom_X, with arbitrary schemes T,T' over S and a fixed map b:T' -> X. The
  two candidate lifts have composite b and agree after the given first-order j.
  Tests are not restricted to affine schemes. `SpaceChartwiseUnramified` uses
  all compatible etale scheme-chart squares and the recorded `IsUnramified`.
- `space_unramified_formally_unramified h hh` is the assertion that every
  chartwise unramified map is formally unramified. It adds no representability,
  finite presentation, quasi-compactness, or separation condition on h.
- `space_universal_firstOrderThickening_exists h hh` supplies W,k,q with the
  existing `IsUniversalSpaceFirstOrderThickening h k q`. Its first two clauses
  say k is first order and k ≫ q = h. Its third quantifies over ALL algebraic
  spaces T,T', first-order j:T -> T', b:T' -> X, and a:T -> Z over X, and
  asserts a unique extension a' with j ≫ a' = a ≫ k and a' ≫ q = b. Scheme
  tests are included by the existing `schemeSpace` embedding.
- `space_universal_conormal` states that the actual small-etale direct image
  `enlargedSmallDirectImage k` is an equivalence of set-sheaf categories, hence
  gives the common topos. `spaceKernel k` is the categorical kernel of the
  actual structural map O_W -> k_*O_Z. `spaceConormal k` is its existing
  tensor pullback to Z. The theorem asserts quasi-coherence of both, and that
  the adjunction unit I -> k_*k^*I is an isomorphism. This is the canonical
  identification on the common topos, with the quotient O_Z action, not an
  arbitrary isomorphism or a chosen unknown module.
- `space_universal_conormal_closed` assumes exactly representable closed
  immersion h, and any universal W,k,q. It says q is closed, with kernel
  ideal equal to the locally generated square of the kernel K of h, on every
  etale chart. Thus W is the closed subspace V(K²). The existing
  `idealPowerSubsheafSections` sheafifies local ideal products; it does not
  incorrectly equate global sections with finite sums of global products.
  The unit K -> h_*h^*K is epi, with kernel K² expressed sectionwise. Thus
  h^*K is K/K² as a sheaf, including its O_Z scalar structure. The final
  uniquely normalized isomorphism identifies this quotient with C_{Z/X}.
  `IsSpaceConormalIdentification` sends 1 tensor s to 1 tensor t whenever
  the actual function pullback sends the ideal section s to t.
- `space_conormal_map` treats EVERY commuting square of first-order thickenings,
  without assuming its vertical maps are etale or invertible. Its unique map
  f^*C_j -> C_i is normalized by `IsSpaceConormalMap` on every compatible chart
  square and ideal section. It sends 1 tensor (1 tensor s) to 1 tensor t
  precisely when the actual ring pullback sends s to t. Together with the
  identical normalization of the closed-immersion comparison this renders the
  final naturality clause. Module linearity extends the formula to all scalars.
  These generator identities make the assertions canonical and exclude freely
  chosen comparison maps. There is no theorem or hypothesis claiming global
  lifting of arbitrary quotient sections.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom` (full signatures
  and docstrings read at lines 42 and 74); scheme tests use `Over S` and Yoneda.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `EtaleSite`, `structureSheaf`, `Modules`.
  These are the recorded sheaf/atlas/small-etale encodings, not copies.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `IsUnramified`, its actual
  conjunction LocallyOfFiniteType and open-immersion diagonal.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and the
  actual Mathlib `SheafOfModules.IsQuasicoherent` predicate; the theorem uses
  that predicate on the same module category.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, the recorded
  general-site `SheafOfModules` abbreviation used by `AlgebraicSpace.Modules`.
- `Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionData`:
  `IsSpaceFirstOrderThickening`; `SpaceUniversalThickeningEtaleTransfer`:
  `IsUniversalSpaceFirstOrderThickening`, with its full all-space signature.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleDirectImage`, `moduleTensorPullback`, `moduleTensorAdjunction`,
  `moduleTensorSection`; `AlgebraicSpaceModuleStructureMap`: `moduleStructureMap`.
  These retain the normalized compatible-chart limit projections and tensor unit.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`:
  `enlargedSmallDirectImage`, the transport of the genuine fibre-product direct
  image along the small/enlarged comparisons. Its owning node's current module
  `AtlasEtaleRestriction` is imported for the proof plan as well.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceArtinRees`:
  `idealPowerSubsheafSections`, which uses covering sieves to sheafify local
  ideal-power membership. No Noetherian or coherent hypothesis is imported
  into our statement; those occur only in the separate Artin-Rees theorem.
- `AlgebraicSpaceIdealClosedSubspaceCorrespondence` supplies the ideal/closed
  subspace proof input. All other recorded proof-dependency modules are imported
  privately: EtaleAtlasPresentation, EtaleRelationQuotient,
  ChartwiseEtalePermanence, AtlasEtaleRestriction, and the upstream
  FlatUnramifiedFormallyEtale and UniversalFirstOrderThickeningExists.
  The Mathlib leaf unramified-formally-unramified is the open-diagonal instance
  and `FormallyUnramified.hom_ext`, whose signatures/docstrings were read.
  Six proof dependencies currently have no Lean record and so have no module
  to import: closed-immersion-atlas-locality, closed-immersion-quasi-coherent-modules,
  formally-unramified-etale-charts, integral-radicial-etale-invariance,
  unramified-etale-compatible-charts, and unramified-geometric-equivalence-relation.
  They are proof obligations for stage 3, not hypotheses added here.

The item's stmt_deps gains four landed definition nodes and the two new
existing:true definition records below. They own the predicates, module operations,
structural map, common-topos functor, and locally generated ideal powers used in
the signatures. No existing dependency record is changed. The theorem nodes
lem-sfb-space-universal-thickening-etale-transfer and
lem-trf-space-enlarged-etale-ringed-site-model remain in proof_deps, unchanged
from the live base. The Artin-Rees theorem is not needed for ideal products;
def-sfb-space-ideal-power-products owns those definitions.

Sources opened: local `spaces-more-morphisms.tex`, sections formally-unramified,
universal-thickening (0606--0608), definition-conormal-sheaf and its functoriality;
local module source of every recorded statement dependency. The old CompactObject
example has been withdrawn and contains no declarations; current modules supply
the copyright/module/public-section/header conventions instead.

Edge cases checked mathematically: empty schemes and spaces (all quantifiers and
zero modules remain meaningful); identity h (K=0, conormal zero, W=Z); a closed
immersion Spec(A/K) -> Spec(A) (W=Spec(A/K²), kernel K/K²); already square-zero K
(W=X); open immersions (zero kernel and universal W=Z); nonreduced test schemes;
non-finitely-generated ideals and non-Noetherian bases; nonrepresentable general
h; arbitrary characteristic. There are no extra field, affine, finite type,
Noetherian, or separation hypotheses. No disputed statement or node correction.

Searches actually run with `msearch.py Q45 lem-sfb-space-universal-conormal`:

- leanfinder, `Universal first order thickening and conormal sheaf of a formally
  unramified morphism of algebraic spaces`: 8 hits, all scheme formal
  unramifiedness and its instances; no space universal thickening or conormal.
- leansearch, `Universal square zero thickening and quasi coherent conormal
  module of a formally unramified algebraic space morphism`: 8 ring/scheme
  formal-unramifiedness hits; no exact match.
- loogle, `AlgebraicGeometry.FormallyUnramified, Algebra.Extension.Cotangent`:
  0 hits.
- grep, `UniversalThickening|universalThickening|conormal`, Mathlib
  AlgebraicGeometry: 0 hits from this logged service query.
- Direct rg and grep of `lean/WeilConjectures` and `lean/Sheaf` for this node id,
  FirstOrder/UniversalThick/conormal/FormallyUnramified and definition names:
  found the existing scheme `formallyUnramifiedConormal`, scheme existence,
  the landed space universal predicate and square-zero predicate, structural
  map, local tensor sections, and locally generated ideal-power sections.
  The scheme declaration requires schemes and does not state this space result.
  No space formally-unramified or conormal definition already exists. The
  `OpenModuliSubstack.SpaceMapIsUnramified` predicate only concerns a map from
  a space to a scheme test and is not the general chartwise space notion.
- `dag/lean_names_upstream.json` searched for universal-thickening/conormal
  names; no exact space match.

Validation: scompile.py compiled the sandbox check and final module cleanly
(23.8 s and 12.5 s), with no warnings/errors. All variables/universes are explicit.
The first compile exposed a missing public import, one unmatched parenthesis,
and two implicitly used binder names; all were fixed before this clean compile.

## Second reading by Q45

A separate pass by the same worker (no agents were started, per the dispatcher
instruction) reread the source, unchanged node, helper definitions and all five
statements. Checked each hypothesis and clause against the mapping above.
The all-space universal property includes scheme tests; formal unramifiedness
uses all scheme tests; no representability was added to a general map. The
closed case uses sheaf-local ideal products and epi, not sectionwise surjectivity.
The conormal comparison is normalized on the actual ring-map image; the map
clause quantifies arbitrary commuting thickening squares. Both zero-kernel
and already-square-zero cases have the expected objects. Every helper belongs
to the owning node and has its source/blueprint docstring. Every theorem is
sorry-only and has the node's relevant full natural-language proof steps.
No statement mismatch was found. The maintainer's independent review remains
separate from this worker's second pass.


## New nodes

`def-sfb-space-universal-first-order-thickening` records the existing
`AlgebraicGeometry.AlgebraicSpace.IsUniversalSpaceFirstOrderThickening` in
`Sheaf.AlgebraicGeometry.SpaceUniversalThickeningEtaleTransfer`, with
`existing: true`, no file and the verbatim signature. Stacks Tag 0601,
section-universal-thickening and equation-universal-first-order-thickening,
defines exactly this predicate: first-order `i`, `i ≫ f' = f`, then every
space test `T,T'`, first-order `j`, map `b` and compatible `a`, and exactly
one `a'` satisfying both triangles. No formal-unramifiedness hypothesis or
existence of a universal object is part of this definition. Its dependencies
are scheme, algebraic space, size convention and the live space first-order
thickening definition. LeanSearch returned eight ring/scheme lifting hits,
Loogle did not know this project identifier, and Mathlib grep returned zero.
Direct DAG/project searches locate only the theorem owner's record and the
published definition at line 38, not a definition-node owner. The scheme-only
universal-first-order-thickening node has different objects and tests.
`blueprint_refs.py ancestor` gives None; search for "universal first-order
thickening" gives zero blueprint nodes. All raw service results are preserved
in this node's mathlib_searches. This adds ownership without a duplicate Lean
construction or a new sorry. Tests with empty spaces, identity maps and
arbitrary non-scheme space tests leave all three predicate clauses meaningful.

`def-sfb-space-small-etale-direct-image` records the existing
`AlgebraicGeometry.AlgebraicSpace.enlargedSmallDirectImage` in
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`, again `existing: true`
and no file. Stacks 03G0/03G1 and 03G2(1),(3) give the enlarged site and the
transported direct image. Its exact real construction is
`(enlargedSetEquivalence X).inverse ⋙ enlargedDirectImage f _ ⋙
(enlargedSetEquivalence Y).functor`, with the same coefficient universe
`Type (max (u + 1) w)` on both sites. The enlarged direct image is actual
precomposition with fibre-product base change, not a chosen arbitrary functor.
The definition requires neither representability nor etaleness of `f`.
Dependencies are the scheme, algebraic space, size and site/sheaf definitions.
LeanSearch returned eight general site, topological-space or scheme results;
Loogle did not know this project identifier; Mathlib grep returned zero.
DAG and project rg finds the theorem record and the real definition at line
550, with no definition owner. The representable abelian-space and scheme
pushforwards have different hypotheses or coefficients. Blueprint search
"small etale direct image" gives zero nodes, and the item's ancestor is None.
The raw results are in mathlib_searches. The empty and identity cases remain
well typed, and arbitrary w retains the source's coefficient size convention.

## Returned H2 repair and self-check

Return read: L, immutable head c5ece337eebe. The report and saved packet were
inspected before any changes. The required first `deliver2.py --no-push`
passed (fa178a59077), confirming that the retained Lean compiles and the saved
packet has valid shape. The current live node differs from that saved node
only in lean and stmt_deps; the accepted mathematical statement, proof and
proof_deps are retained. This is a substantive metadata repair of all three
ownership defects, not an unchanged re-push:

- IsUniversalSpaceFirstOrderThickening now has the new existing:true definition
  owner above, replacing the transfer theorem in the added statement dependencies.
- enlargedSmallDirectImage now has the second existing:true definition owner,
  replacing the enlarged-site theorem in the added statement dependencies.
- idealPowerSubsheafSections now cites the live
  def-sfb-space-ideal-power-products, rather than lem-sfb-space-artin-rees.

The two theorem proof dependencies were retained unchanged. The Lean file
is byte-identical to the retained returned packet, SHA256
518cd662d277a57b74b634ab86b81359d00e5bed24ba497a9c5eaa6a17ac1b30.
There are no new Lean files, declaration copies or statement changes. Every
new node has the exact stage-2 field set, source, three search kinds and the
inherited blueprint ancestry. A second reading by Q45 checked each new
statement against its existing definition's full signature and body, including
both universal-property triangles and the direction of both comparison
functors; no mismatch was found. No other agent was started. The maintainer's
independent review remains separate.


Repair validation: `scompile.py Q45 lem-sfb-space-universal-conormal` compiled
both the sandbox check and retained library module cleanly (23.8 s and 12.5 s).
The repaired dry run requested the current required `import_flags` field on both
new nodes; both now carry `import_flags: []`. No Lean warning or error occurred.
The local self-check verified verbatim existing signatures, exact cited-definition
sets, byte identity of the Lean file and absence of dependency cycles. Final
`deliver2.py --no-push` is run on this complete packet before delivery.
