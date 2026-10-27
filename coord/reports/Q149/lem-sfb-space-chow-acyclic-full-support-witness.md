## Worker report

Item: `lem-sfb-space-chow-acyclic-full-support-witness`.
Module: `Sheaf.AlgebraicGeometry.SpaceChowAcyclicFullSupportWitness`.
Declaration: `AlgebraicGeometry.AlgebraicSpace.exists_chow_acyclic_fullSupport_witness`.
This delivery states the existential projective-twist witness, with one `sorry` and no
new definitions or proved theorems. The theorem docstring gives all eight accepted proof
steps, including independent projective coherence, one-row Leray degeneration, the counit
support argument and the reduced-chart annihilator calculation.

Read the node, every statement dependency and its recorded source signature/docstring,
the stage-2 contract, delivery-errors H, and the current CompactObject example (the Sheaf
file is withdrawn, so its recorded upstream module was read as well). The source checked
is `literature/stacks-project/spaces-cohomology.tex`, lemma-proper-pushforward-coherent,
Tag 08AR, especially lines 3679–3791. Its displayed graph target and stalk arrows contain
the typos already corrected in the DAG proof; this delivery preserves the DAG statement.

Hypotheses and objects, clause by clause:

- A scheme S: `{S : Scheme.{u}}`. Algebraic spaces and all modules are over this S.
- A Noetherian commutative ring A: `(A : CommRingCat.{u}) [IsNoetherianRing A]`.
- Spec A as an S-scheme: `(a : Spec A ⟶ S)`. This supplies precisely the structural
  morphism implicit in a morphism of algebraic spaces over S, without restricting S.
- Z and its morphism to Spec A: `(Z : AlgebraicSpace S)` and
  `(g : Z ⟶ schemeSpace (Over.mk a))`. `schemeSpace` is the actual representable sheaf.
- Proper g: `(hg : MapIsProper g)`, the recorded conjunction of representable closed
  diagonal, quasi-compact chartwise finite type and universal closedness on point spaces.
- Nonempty Z: `(hne : Nonempty (Point Z.obj.obj))`.
- Reduced Z: `(hred : ∀ U : Z.EtaleSite, IsReduced (Z.etaleForget.obj U))`.
- Irreducible Z: `(hirr : IrreducibleSpace (Point Z.obj.obj))`, with the recorded atlas
  topology. No chosen atlas, generic point, finiteness of S, or separate Noetherian
  hypothesis on Z has been added. Noetherianity of Z follows in the proof from properness.
- The two `HasDerivedCategory.{w}` instance arguments are the size/implementation
  interface for the existing derived category, for source and target only. They impose
  no equality between site object, site morphism and coefficient universes. The
  localization morphism universe w is arbitrary. This infrastructure is available by
  the standard construction (Mathlib `HasDerivedCategory.standard`); it is not an
  additional geometric hypothesis.

Witness and conclusions, clause by clause:

- Integers n,d >= 0 are `∃ (n d : ℕ)`. n is projective dimension, so the coordinate
  type is `ULift.{u} (Fin (n + 1))`, exactly n+1 homogeneous coordinates.
- The scheme T with its S-structure is `T : Over S`. Its representing space is
  `schemeSpace T`. The immersion is the underlying scheme map `j.left`, with
  `j : T ⟶ Over.mk ((ProjectiveSpace ... (Spec A) ↘ Spec A) ≫ a)`.
- The proper surjective pi is `π : schemeSpace T ⟶ Z`, together with `MapIsProper π`
  and `Function.Surjective (mapPoint π.hom.hom)`. Surjectivity is on point classes,
  not a representability assumption on pi.
- j is closed by `IsClosedImmersion j.left`.
- p is the projective projection over S: its underlying map is constrained by
  `p.left = (ProjectiveSpace ... (Spec A) ↘ Spec A)`. An Over morphism is determined
  by its underlying map, so this is a uniquely specified canonical projection.
- k has target the presheaf fibre product of `yoneda.map p` and `g.hom.hom`, and
  its composites with the two projections are constrained to `yoneda.map j` and
  `π.hom.hom`. The pullback universal property uniquely determines k as (j,pi).
  These equations also assert that the diagram is over Spec A; j's domain structure
  is therefore the same structure induced by g pi. There is no arbitrary comparison map.
- Clause (a) is `IsRepresentableWith (fun _ _ f ↦ IsClosedImmersion f.left) k`.
  Scheme tests give exactly closed immersion into projective space times Z over Spec A.
- The actual scheme module L is `(Scheme.Modules.tensorPullback j.left).obj
  (ProjectiveSpace.twist ... (Spec A) 1)`. Its power is the existing `.tensorPow d`.
- M is its corresponding small-etale module on the represented T: it is quasi-coherent,
  and on every etale scheme chart U its `schemeRestriction` is isomorphic to the tensor
  pullback of that very `.tensorPow d` along `chartToScheme T (𝟙 _) U`.
  This uses the fixed restriction functor, with no invented etale extension. The identity
  chart of T is included. For quasi-coherent modules, Zariski/etale comparison is fully
  faithful; hence its identity-chart restriction already determines M up to isomorphism.
  All the chart conditions are the usual pullback formula of that same module, rather
  than an arbitrary collection of descent objects. No uniqueness/existence theorem is
  used to define data.
- G is constrained by `Nonempty (G ≅ (moduleDirectImage π).obj M)`. Thus it is exactly
  pi_*(L tensor-power d), up to the equality notion used for categorical constructions.
- Clause (b), coherence: `G.IsQuasicoherent` and the actual `RingedSpace.IsCoherent`
  predicate on `((Z.schemeRestriction U).obj G)` for every etale scheme chart U.
  This retains finite type and the finite-type-kernel condition; it does not replace
  coherence by an unsupported finite-presentation abbreviation.
- Clause (b), full support: `moduleSupport G = Set.univ`, the existing nonzero-geometric-
  germ support, not merely nonzero global sections or ordinary points of one atlas.
- Clause (b), Ann(G)=0: for every chart U and scalar r in O(U), if its restriction kills
  every section of G on every chart V -> U, then r=0. The antecedent is exactly that
  r is a section of the sheaf annihilator. Testing every further restriction is essential;
  annihilation of G(U) alone would not state the local sheaf annihilator condition.
- Clause (c), coherent g_*G: the identical quasi-coherence and chart-coherence predicates
  applied to `(moduleDirectImage g).obj G` on the represented Spec A.
- Clause (c), positive higher images: for every `q : ℕ` with `0 < q`, `IsZero` of the
  q-th homology of `(derivedDirectImage g)` on G placed in degree zero via the actual
  `smallModuleRestriction`, transported back by `smallModuleEquivalence.inverse`.
  This is the canonical right derived direct image of all module sheaves, not of QCoh.
  For G in degree zero its bounded-below injective-resolution computation agrees with
  this K-injective implementation. Degree zero is handled by the preceding coherence
  clause; no degree-zero vanishing is asserted.
- All existential data are bound once outside all these clauses. There is no assertion
  for every exponent or arbitrary projective cover.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.EtaleSite`, `.Modules`, `.structureSheaf`, `.IsRepresentableWith`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: the existing site
  quasi-coherence interface/QCoh, using Mathlib `SheafOfModules.IsQuasicoherent`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImage` and
  its normalized compatible-chart model (the tensor pullback adjunction is retained).
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian` (chart convention
  in the source proof); `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: public `RingedSpace.IsCoherent`
  from `WeilConjectures.AlgebraicGeometry.Coherent`, used for all chart coherence.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`;
  its canonical `mapPoint` is publicly available through the morphism-properties module.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveSpace`, its
  structural morphism. `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `IsClosedImmersion`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`: `ProjectiveSpace.twist`;
  the same public upstream module exposes `Scheme.Modules.tensorPow` and tensor pullback.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded
  independent-universe tensor interface; the actual power used is the upstream scheme
  tensor power, using that scheme's established tensor structure.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and `.Resolution`:
  `Injective`, `InjectiveResolution`, the resolution convention in the statement.
- Four already-landed notion owners are added to stmt_deps, with no changes to any
  dependency record: `def-trf-scheme-algebraic-space` (`schemeSpace`, module
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`);
  `def-trf-space-module-scheme-restriction` (`schemeRestriction`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`);
  `def-sfb-space-module-support` (`moduleSupport`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport`);
  `def-sfb-space-derived-module-calculus` (`derivedDirectImage`, `chartToScheme`,
  `smallModuleRestriction`, `smallModuleEquivalence`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`). Their node statements and
  complete source declarations/docstrings were read. These additions give the existing
  interfaces explicit DAG ownership; no new node or dependency-module repair is needed.

The stated proof dependencies' modules are imported without `public`, including chart
fibre products, closed-immersion products, etale pushforward restriction, the Zariski/etale
comparison, independent projective finite type, locally Noetherian coherence, ample
invertible projective twists, chart support, finite-type support and radical equality.
Mathlib affine/qcqs and closed-immersion inputs are imported too. The other space-specific
proof dependencies have no recorded statement yet; their proof steps remain fully named
in the docstring and no replacement theorem is invented.

Edge cases checked before writing and again on the signature:

- n=0 has one coordinate, hence projective zero-space, not empty projective space.
- d=0 uses the existing tensor unit by `tensorPow_zero`; the docstring uses section 1.
- Empty Z is excluded explicitly as in the node; the zero ring cannot furnish such a
  nonempty source over its empty spectrum. The empty chart causes no false nonzero claim.
- No characteristic, perfection, finite type of the ring over a prime ring, or reducedness
  of A is assumed. Reducedness belongs only to all etale charts of Z.
- Noetherianity of Z is a consequence, not an additional binder. The actual ringed-site
  section universe remains u and no site object/morphism universe equality is forced.
- The annihilator test includes all refinements and hence is valid on nonaffine charts.
- Only q>0 vanishes; degree zero can be a nonzero finite module.

Searches actually run (Q149 wrapper, same item):

1. `msearch.py ... leanfinder "A proper integral algebraic space over a Noetherian ring
   has an acyclic faithful coherent module obtained by a projective Chow cover and twist"`:
   OK, 8 hits. These were scheme affine/Noetherian/limit facts, including
   `AlgebraicGeometry.noetherianSpace_of_isAffine` and `IsLocallyNoetherian`; no match
   for the algebraic-space existential witness.
2. `msearch.py ... loogle "AlgebraicGeometry.ProjectiveSpace.twist,
   Functor.rightDerived"`: 0 hits; Loogle reported the project-local twist identifier
   unknown. This is a search-service index limitation, not evidence that the twist is
   absent: its recorded upstream source was opened and used.
3. `msearch.py ... grep "chow|Chow|acyclic.*support" AlgebraicGeometry`: 0 Mathlib hits.
4. `rg -n 'chow|Chow|acyclic.*support' lean/WeilConjectures lean/Sheaf`: found scheme
   Chow constructions, `ChowTwistFiniteCohomology`, `ChowFiniteCohomologyWitness`, and
   derived-Chow neighbourhood/transform results. They are respectively scheme-only
   finite-cohomology witnesses or different derived-neighbourhood statements, not this
   algebraic-space acyclic faithful witness. Existing projective twists and support
   definitions were reused, as listed above.
5. `grep -rn 'lem-sfb-space-chow-acyclic-full-support-witness' lean/WeilConjectures`:
   no matches. Searches of `AlgebraicSpace*.lean` located all chart and support interfaces.

Validation: prescribed `scompile.py Q149 <item> <module file>` succeeded twice. The final
import-complete version compiled as sandbox and real module, both without errors or
non-sorry warnings (2.2 s / 2.1 s on the second run). `autoImplicit` is false and all
universes are explicit. No statement correction, STATEMENT-DISPUTED issue, new node,
hollow definition, or live-repository edit is present.

## Second reading by Q149

A separate in-thread rereading compared the node and the completed signature; no second
agent was started, in accordance with the dispatcher's instruction. The maintainer's
independent delivery review remains the independent reading.

Checked each hypothesis against the binders and each of (a), (b), (c) against the nested
conjunctions. In particular, j is a scheme closed immersion, pi is proper in the chartwise
sense and surjective on points, k is forced by both product projections, and the twist
is pulled back from O(1) with d a single existential natural number. The module M is pinned
by its actual chart restrictions including the identity chart, and G by the canonical
compatible-chart direct image. Coherence uses the full kernel condition on every chart.
The support equals all point classes, while faithfulness separately tests the sheaf
annihilator on all refinements. Both degree-zero coherence and every positive higher
image are included. No conclusion about all twists, a generic-point-only support, ordinary
cohomology groups in place of sheaf higher images, or an arbitrary direct-image functor
has slipped in. No mismatch required a change to the node statement. The second pass
added explicit imports of the recorded definition modules and the four already-landed
notion-owner stmt_deps, then the completed import list was recompiled cleanly.
