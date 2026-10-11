## Worker report

Module: `Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent`.
Declaration: `AlgebraicGeometry.Scheme.exists_finiteEtale_lift_of_henselianPair_of_gRing_lifting`.
This states the conditional reduction, not the unconditional lifting theorem. Its sole proof is
`sorry`; no definition or auxiliary proof is added. The node copy changes only `lean`.

Source checked: https://stacks.math.columbia.edu/tag/0GS2, proof, “General case”. The local
`literature/stacks-project/pione.tex` was absent, so I read the official source online.
The source reduces lifting through proper finite-type approximations and henselizations of
finite-type ℤ-algebras. The declaration docstring gives all eight node proof steps and their
named dependencies; these proof dependencies are not imported for a stage-2 statement.

Hypothesis and clause matching:

- (H), for every commutative ring B: `H : ∀ (B : Type u) [CommRing B], ...`.
- B is a G-ring (including Noetherian): `IsGRing B →`. The recorded definition includes
  `IsNoetherianRing B`; there is no extra hypothesis on B.
- (B,J) is henselian: `∀ (J : Ideal B) [HenselianRing B J] ...`.
- Every proper Z → Spec B: `(Z : Scheme.{u}) (g : Z ⟶ Spec (.of B)) [IsProper g]`.
- Z₀ = Z × Spec(B/J): `pullback g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))`.
- Every finite étale W over Z₀: `W` is in `(@IsFinite ⊓ @Etale).Over ⊤ Z₀`.
  The object property imposes both finiteness and étaleness; `⊤` allows all base morphisms.
- (H) supplies a finite étale Z-scheme U': the existential binder uses the same property
  subcategory over Z.
- (H) supplies U' × Z₀ ≅ W over Z₀: `Nonempty (Over.mk (pullback.snd U'.hom
  (pullback.fst g ...)) ≅ Over.mk W.hom)`. An isomorphism in `Over Z₀` includes the
  compatibility of both its maps with the structure maps. A bare scheme isomorphism would
  have omitted this compatibility. `Nonempty` expresses existence of the isomorphism.
- Arbitrary henselian (A,I): `{A : Type u} [CommRing A] (I : Ideal A)
  [HenselianRing A I]`; no G-ring, Noetherian, completeness or local-ring assumption on A.
- Proper f : Y → Spec A: `{Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]`.
- Closed fibre Y₀: the same pullback expression with A,I,f.
- Finite étale V over Y₀: the binder `V` uses the same finite étale category as W.
- Conclusion finite étale U over Y: the existential binder uses that category over Y.
- Conclusion U × Y₀ ≅ V as Y₀-schemes: the concluding `Nonempty` of the iso between
  `Over.mk (pullback.snd U.hom (pullback.fst f ...))` and `Over.mk V.hom`.
- The parenthetical essential-surjectivity reformulation adds no full-faithfulness assertion.

Dependencies read and used:

- `def-weil-pbc-henselian-terminology`: `Sheaf.RingTheory.HenselianTerminology`, with the
  recorded existing `HenselianRing` from `Mathlib.RingTheory.Henselian`. Read the class's
  root-lifting signature and docstring, the project module, and the upstream Henselian
  module confirming this is the project's chosen henselian-pair notion.
- `def-weil-pbc-g-ring`: `Sheaf.RingTheory.GRing`, `IsGRing`; read all definitions there,
  including regular maps, geometric regularity and the Noetherian clause.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`; read its class and docstring. Universal closedness gives
  quasi-compactness, so locally finite type here agrees with the node's finite type.
- `def-pc-fibre-product`: the Mathlib leaf's `CategoryTheory.Limits.pullback`, `pullback.fst`
  and `pullback.snd` in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
  Read their signatures/docstrings and the universal-property construction `pullback.lift`.
- `def-weil-pbc-finite-etale-category`: the Mathlib leaf's `MorphismProperty.Over` in
  `Mathlib.CategoryTheory.MorphismProperty.Comma`. Read the property-category definition
  and its constructors. Also read `MorphismProperty.Over.pullback` in
  `Mathlib.CategoryTheory.MorphismProperty.OverAdjunction`: its object's structure map is
  exactly `pullback.snd`, which is the unbundled base change used in the conclusion.
- `lem-weil-pbc-finite-etale-lifting-approximation`:
  `Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation`,
  `AlgebraicGeometry.Scheme.exists_finiteEtale_lift_of_henselianPair_of_isGRing`.
  Read its full statement and proof docstring. H explicitly quantifies its exact statement,
  with B,J,Z,g,W in place of A,I,Y,f,V. The theorem itself is not invoked: this node proves
  the reduction conditional on H. Its module is the only import and provides every notion
  required by the signature transitively, without duplicate definitions.

Edge cases checked before writing: the empty proper scheme and empty finite étale cover are
allowed; no nonemptiness, connectedness, positive degree, field or characteristic assumption
is present. The zero ring is allowed by `[CommRing A]` and gives the empty spectrum.
I = 0 gives the whole fibre and trivial lifting. Henselian pairs already include the Jacobson
condition through their recorded class; I = ⊤ is possible only for the zero ring. The universe
u is explicitly declared and arbitrary. As in the approximation dependency, the ring and
schemes are small in u; finite-type ℤ approximations and their henselizations can be realized
in this same universe, including u = 0. No indexing set is restricted or introduced by this
statement. Every type, ring instance, morphism, ideal and universe is explicitly bound.

Searches for an existing declaration (all via `msearch.py J1 <item>` unless stated):

- LeanSearch query `lifting finite etale covers over henselian pairs from Noetherian G-rings`:
  service unavailable (Internal Server Error); no verdict based on the unavailable service.
- LeanFinder query `Finite etale lifting over arbitrary henselian pairs reduces to lifting
  over Noetherian G-ring henselian pairs`: eight hits, including HenselianLocalRing,
  Algebra.Etale.exists_subalgebra_fg and standard étale lifting; no proper-scheme reduction.
- Loogle query `HenselianRing, AlgebraicGeometry.IsProper`: zero hits.
- Mathlib grep query `henselian.*(lift|finite)|finiteEtale.*(lift|henselian)` in
  `AlgebraicGeometry`: zero hits.
- `rg -n 'finiteEtale.*lift|henselianPair|lem-weil-pbc-finite-etale-lifting-limit-descent'`
  in the upstream `WeilConjectures` tree and project's `lean/Sheaf`: only the distinct
  G-ring approximation theorem in `FiniteEtaleLiftingApproximation.lean`; no reduction.
- Search of `dag/lean_names_upstream.json` for `finiteEtale.*lift|henselianPair`: no hits.
  The chosen declaration name has no existing match.

No statement correction, dispute, new definition node or dependency repair is needed.

Validation: server single-file compilation and `deliver2.py --no-push` dry run; results
recorded after execution below. The independent second-reading section is left to the next
worker, as required by the dispatcher brief.


## Second reading by J1

I independently read the sandbox node and Lean module, the six statement dependency
nodes, their recorded declarations and docstrings, and the source. The local Stacks tree
is absent; I fetched the official `stacks/stacks-project` `pione.tex` into this item's
scratchpad, reading lines 1749–1761 and 1849–1881 (Tag 0GS2, especially “General case”).
I also checked https://stacks.math.columbia.edu/tag/0GS2. The source assumes a commutative
ring, a henselian pair and a proper scheme, with no Noetherian hypothesis in the general
case. Its finite-type approximations and henselizations explain the conditional reduction
in this node. The node deliberately isolates essential surjectivity, not full faithfulness.
There is no `statement_change`, no new node and no dependency module in this delivery.

The object/hypothesis/conclusion list I made from the node before matching the Lean:

| Node item | Lean rendering and verdict |
| --- | --- |
| Hypothesis (H), universally over commutative rings B | `H : ∀ (B : Type u) [CommRing B], ...`; correct, an actual universally quantified lifting assumption. |
| B a G-ring, including Noetherianity | `IsGRing B →`; correct. The definition begins `IsNoetherianRing B ∧ ...`, so Noetherianity is neither dropped nor added separately. |
| J an ideal with (B,J) henselian | `∀ (J : Ideal B) [HenselianRing B J] ...`; correct, not a local-ring or maximal-ideal specialization. |
| Every scheme Z and proper g : Z → Spec B | `(Z : Scheme.{u}) (g : Z ⟶ Spec (.of B)) [IsProper g]`; correct. |
| Closed fibre Z₀ | `pullback g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))`; correct, the quotient morphism has source Spec(B/J). |
| Every finite étale W → Z₀ | `(W : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Z₀)` with Z₀ expanded; correct, conjunction of both properties and all base morphisms. |
| (H) produces a finite étale U′ → Z | `∃ U' : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Z, ...`; correct, after W in the quantifier order. |
| (H) produces U′ ×_Z Z₀ ≅ W as Z₀-schemes | `Nonempty (Over.mk (pullback.snd U'.hom (pullback.fst g ...)) ≅ Over.mk W.hom)`; correct. The first projection is Z₀ → Z; the second projection of the subsequent pullback is its structure map to Z₀. `Over` enforces compatibility with that base. |
| Arbitrary commutative ring A and henselian ideal I | `{A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]`; correct. There is no G-ring, Noetherian, completeness, domain or local-ring assumption on A. |
| Scheme Y and proper f : Y → Spec A | `{Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]`; correct. |
| Closed fibre Y₀ | `pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))`; correct. |
| Arbitrary finite étale V → Y₀ | `V` in the same property-over category, with Y₀ expanded; correct. |
| Existence of a finite étale U → Y | Concluding `∃ U : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y`; correct. |
| Isomorphism U ×_Y Y₀ ≅ V over Y₀ | Concluding `Nonempty (Over.mk (pullback.snd U.hom (pullback.fst f ...)) ≅ Over.mk V.hom)`; correct. No bare scheme isomorphism or unique lifting claim replaces the specified conclusion. |
| Parenthetical reformulation as reduction of essential surjectivity | Exactly the assumption H and the concluding existential; correct, no extra full-faithfulness assertion. |

Dependency reading, below the names:

- `HenselianTerminology.lean` explicitly identifies `HenselianRing` as the chosen pair
  notion. I read Mathlib's class at `RingTheory/Henselian.lean:94`: its fields are the
  Jacobson containment and monic-polynomial simple-root lifting. The dependency node
  records the equivalence with its finite-algebra idempotent characterization (09XI (3)).
  I also read the upstream `WeilConjectures/Mathlib/RingTheory/Henselian.lean`; it confirms
  this same notion and includes the zero-ideal case. No second henselian definition occurs.
- I read every definition in `GRing.lean`: geometric regularity tests finite purely
  inseparable extensions in `Type (max u v)`; regularity is flatness plus geometrically
  regular residue-field fibres `p.Fiber S`; `IsGRing` imposes Noetherianity and regularity
  of each prime-localization-to-completion map. These are the dependency node's notions.
- Mathlib's `IsProper` extends separatedness, universal closedness and locally finite
  type. I read `UniversallyClosed` and its `QuasiCompact` instance at line 167, so this
  is precisely the finite-type properness required by the node, without added assumptions.
- Mathlib's `pullback`, `pullback.fst`, `pullback.snd` and `pullback.lift` in
  `Limits/Shapes/Pullback/HasPullback.lean` implement the recorded universal property.
  All pullbacks in the statement are schemes, for which pullbacks exist.
- I read `MorphismProperty.Over` and `Over.mk` in `MorphismProperty/Comma.lean`, the
  actual object formula of `MorphismProperty.Over.pullback` in `OverAdjunction.lean`,
  and `CategoryTheory.Over.mk`/`Over.isoMk` in `Comma/Over/Basic.lean`. The category's
  parameter `⊤` restricts no morphisms; the pullback functor's structure map is precisely
  `pullback.snd`. I also read `IsFinite` and `Etale` in their Mathlib morphism files.
- I read `FiniteEtaleLiftingApproximation.lean` in full. Its theorem has exactly the
  B,J,Z,g,W conclusion quantified by H (renaming the binders). The import exposes all
  the recorded definitions; the reduction does not apply the approximation theorem
  as a proof in stage 2.

Edge cases: `[CommRing A]` permits the zero ring and imposes no characteristic or domain
restriction. The empty Y and empty V are permitted; there is no nonempty, connected,
surjective or positive-degree requirement. I = 0 permits the entire scheme as closed
fibre; I = ⊤ is compatible with the henselian Jacobson condition only in the zero ring.
There is no index type or natural-number parameter to constrain (in particular, no n = 0
case is excluded). The declared universe u is arbitrary, including zero. H ranges over
rings in the same universe as A and schemes in that same universe, so it is not a test
hypothesis in an independently smaller universe. Finite-type integer models and their
henselizations can be represented in u. All variables and universes are bound explicitly.

Independent H4 searches, using different concept queries from the first reader:

- `msearch.py ... leanfinder "essential surjectivity of restriction of finite étale schemes
  from proper schemes to closed fibres for general henselian ideals"`: eight hits for
  standard étale algebras, scheme étale categories, full forgetful functors and pointsPi;
  no conditional G-ring reduction.
- `msearch.py ... loogle "IsGRing"`: no hits; this project definition is unknown to
  Loogle, so this is not evidence against a matching project theorem.
- `msearch.py ... leansearch "Reduction from arbitrary henselian rings to G-rings for
  finite étale covers of proper schemes"`: service unavailable, Internal Server Error;
  recorded as unavailable, no negative verdict inferred.
- `rg -n -i 'henselian.*proper|proper.*henselian|gRing_lifting|finite.etale.*(reduc|limit.descent)'`
  on upstream `WeilConjectures`, project `lean/Sheaf`, and Mathlib `AlgebraicGeometry`
  found the upstream `HenselianFiniteEtale.lean`, connectedness and H⁰ modules, and the
  project's approximation and essential-surjectivity modules. I opened
  `HenselianFiniteEtale.lean` in full and the project essential-surjectivity module.
  The upstream theorem asserts an unconditional equivalence of categories; the project
  theorem asserts unconditional lifting. Neither is this conditional reduction with H.
  `rg 'gRing_lifting' dag/lean_names_upstream.json` found no duplicate declaration.

H5–H9: the module introduces no definitions, private notions or auxiliary proofs. Its only
proof is the named theorem's `sorry`. The module and theorem docstrings give the source
and correct blueprint id. I matched all eight proof-docstring steps to the node's eight
steps: proper approximation, ideals/quotients, closed-fibre limits, finite étale descent,
henselization/G-rings, lifting via H, base change, and the fibre isomorphism by pasting.
The single import is used transitively for the signature and matches the approximation
dependency. Namespace and file placement follow project conventions; every line is at
most 100 characters.

Mismatches and repairs: none. I preserved the Lean and node unchanged and appended this
independent reading to the worker report. A direct string comparison confirms that
`lean.statement` equals the file's signature verbatim, excluding `:= by`. The sandbox
node differs from the repository node only in `lean`.

Validation: `scompile.py J1 lem-weil-pbc-finite-etale-lifting-limit-descent` on the delivered
module compiled successfully on the server in 1.7 seconds, exit 0, with no warnings.
