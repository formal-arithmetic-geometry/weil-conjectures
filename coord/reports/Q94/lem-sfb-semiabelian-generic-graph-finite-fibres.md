## Worker report

The module `Sheaf.AlgebraicGeometry.SemiabelianGenericGraphFiniteFibres` states
`AlgebraicGeometry.semiabelian_generic_graph_finite_fibres` with proof `sorry`.
It also constructs `semiabelianGenericGraphMap` and
`semiabelianGenericGraphProjection`, two helpers belonging to this node and listed
in `lean.declarations`. Both definitions have real data, with no postponed proofs.
The node copy changes only `lean`. There are no new nodes, dependency repairs,
statement corrections, or statement disputes.

Source read: Faltings, *Finiteness Theorems for Abelian Varieties over Number
Fields*, Chapter II, section 2, Lemma 1 proof, printed pp. 10-11, at
https://www-fourier.univ-grenoble-alpes.fr/~lefourns/contenu/Zywina/Faltings.pdf .
The graph-projection assertion is on printed p. 10 (PDF page 2); the proof
continues on printed p. 11. It asserts singleton fibres; this node asks only for
finite underlying point sets. The local file is still marked WANTED. The current
blueprint unit `_section.md` in `literature/blueprint/latest/` was read; this is an
auxiliary node of the inherited independent power-prolongation route, not the
unit's statement. The module docstring carries all six accepted proof steps.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A scheme S | `{S : Scheme.{u}}` |
| Integral S | `[IsIntegral S]`, including nonemptiness |
| Locally Noetherian S | `[IsLocallyNoetherian S]` |
| Normal means every local ring is an integrally closed domain | `hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s)` |
| P and Q are group schemes over S | `P Q : Grp (Over S)`; the group-object structure contains multiplication, identity, inverse, and their identities as morphisms over S |
| Commutative group laws | `[IsCommMonObj P.X] [IsCommMonObj Q.X]` |
| Smooth structure morphisms | `[Smooth P.X.hom] [Smooth Q.X.hom]` |
| Separated, meaning closed diagonal | `[IsSeparated P.X.hom] [IsSeparated Q.X.hom]`; Mathlib defines this by `IsClosedImmersion (pullback.diagonal f)` |
| Finite presentation | `[LocallyOfFinitePresentation P.X.hom] [QuasiCompact P.X.hom]` and the same for Q; separatedness supplies quasi-separatedness |
| Semiabelian geometric fibres | `hP : HasSemiabelianGeometricFibres P` and `hQ : HasSemiabelianGeometricFibres Q`, using the recorded split-torus-kernel and fppf-locally-surjective quotient definition |
| Generic point eta and K = kappa(eta) | `genericPoint S` and `S.fromSpecResidueField (genericPoint S) : Spec (S.residueField (genericPoint S)) ⟶ S` |
| Generic fibres with their induced group laws | `(Over.pullback (S.fromSpecResidueField (genericPoint S))).mapGrp.obj P` and the same for Q; their underlying schemes are exactly the chosen pullbacks defining `P.X.hom.fiber (genericPoint S)` and Q's fibre |
| Given a K-group homomorphism u | `uη` is a morphism between these group objects over `Spec (S.residueField (genericPoint S))`, not an arbitrary scheme map |
| Prescribed map P_eta -> (P times_S Q)_eta -> P times_S Q | `semiabelianGenericGraphMap P Q uη`; its first coordinate is the pullback counit for P, and its second is `uη.hom.hom` followed by the pullback counit for Q |
| Chosen fibre product P times_S Q | The two maps over S are paired by `prod.lift` in `Over S`; `(Over.prodLeftIsoPullback P.X Q.X).hom` takes the underlying product to `pullback P.X.hom Q.X.hom` with the prescribed coordinates |
| Gamma is the scheme-theoretic image | `(semiabelianGenericGraphMap P Q uη).image`, the existing Mathlib scheme image, not a topological or reduced closure |
| pi is its first projection | `semiabelianGenericGraphProjection P Q uη := (semiabelianGenericGraphMap P Q uη).imageι ≫ pullback.fst P.X.hom Q.X.hom` |
| Every point x in P | `(x : P.X.left)` is arbitrary |
| Gamma_x = Gamma times_P Spec kappa(x) | `(semiabelianGenericGraphProjection P Q uη).fiber x` is exactly Mathlib's scheme fibre |
| Its underlying point set is finite | `Finite ((semiabelianGenericGraphProjection P Q uη).fiber x)`, using the scheme-to-underlying-type coercion |
| No reducedness assertion | No `IsReduced`, domain, nonemptiness, or subsingleton conclusion is imposed on this fibre |

The graph helper is the prescribed composite, written directly using its two
coordinates by the fibre-product universal property. It does not assume a
homomorphism extending u, choose an arbitrary map, or choose an arbitrary image.
The counit at an over-object with structure map f has underlying map
`pullback.fst f (S.fromSpecResidueField (genericPoint S))`. Consequently its
coordinates are exactly `P.X.hom.fiberι (genericPoint S)` and
`uη.hom.hom.left ≫ Q.X.hom.fiberι (genericPoint S)`. The intermediate generic
product may be suppressed because its projection to the total product has these
same two coordinates. The recorded `Over.prodLeftIsoPullback` projection
identities were read in `Mathlib.CategoryTheory.Limits.Constructions.Over.Products`.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`.
- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed`, together with `IsDomain`, inline on each stalk as the
  item's normality clause requests.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`; `QuasiCompact` and the
  separated-implies-quasi-separated instance complete finite presentation.
- `def-sfb-semiabelian-geometric-fibres`:
  `Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres`,
  `AlgebraicGeometry.HasSemiabelianGeometricFibres`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, and `pullback.snd`, available
  through the public scheme-fibre and over-product imports.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber` (and the canonical projection interfaces).
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField`, `Scheme.fromSpecResidueField`.
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`; used through the recorded image inclusion
  and Mathlib's separatedness definition in `Morphisms.Separated`.
- `def-nagata-scheme-theoretic-image`:
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`,
  `AlgebraicGeometry.Scheme.Hom.image` and `Scheme.Hom.imageι`.

Every already stated proof dependency's module is imported, privately when it
is needed only for the future proof: semiabelian geometric power integrality,
the algebraic-closure test for geometric connectedness, the smooth connected
generic geometry core, specialization traits, semiabelian trait homomorphism
extension, common extension fields, proper/smooth base change, finite
presentation under ring base change and composition, algebraic closure, and
Noetherian topological spaces. Mathlib proof matches for Noetherian ascent and
scheme image are already public statement imports. At the time of reading,
`lem-sfb-semiabelian-trait-specialization-agreement` had neither a Lean record nor
a Mathlib match; it is a proof dependency only, so no missing notion is required
to state this theorem, and its as-yet nonexistent module is not imported.
There is no import of the downstream normal-semiabelian-hom-extension theorem.

Edge cases checked before writing:

- Empty base schemes are excluded by the node's integrality, not by a new
  assumption. Identity sections force nonempty group fibres. Empty graph
  projection fibres remain permitted by the conclusion `Finite`.
- Torus rank zero, abelian quotient of dimension zero, and the trivial group are
  allowed by the recorded geometric-fibre definition and `Grp (Over S)`.
- Over a field S, the generic base change is canonically the original group;
  the graph of any group homomorphism has the expected single point over each
  source point. Over a DVR, the statement includes degeneration of abelian
  fibres to toric fibres; properness of P or Q is never assumed.
- For split multiplicative groups, the identity, power homomorphisms (including
  power zero), and arbitrary characteristic fit exactly the binders. The graph
  projection, rather than the power map itself, is the morphism whose fibres
  are asserted finite. In particular inseparability of a power map does not
  introduce an unjustified reducedness claim.
- The conclusion does not assert a finite morphism, properness, surjectivity,
  reducedness, or scheme-theoretic length one. It asserts only the node's
  point-set finiteness.
- A single explicit universe `u` covers the base, both group schemes, their
  residue fields and pullbacks. No independent smaller test-field universe is
  introduced; the existing geometric-fibre definition is used verbatim.

Searches performed (actual tool calls):

1. `msearch.py ... leanfinder`, query
   `The scheme theoretic closure of the graph of a generic homomorphism of semiabelian schemes has finite fibres over its first projection`:
   eight hits, including `instFiniteCarrierCarrierCommRingCatFiberOfIsFinite`,
   `IsFinite.finite_preimage_singleton`, `Scheme.Hom.discrete_fiber`, finite and
   locally-quasi-finite pullback instances, and unrelated range/closure results.
   The finite-fibre hits require `[IsFinite f]`; none establishes the graph result.
2. `msearch.py ... loogle`, query `"fiber", "image"`: twelve hits on finset/set
   fibres, topological irreducibility, and prime-spectrum fibre equivalences;
   no semiabelian graph theorem.
3. `msearch.py ... grep`, query
   `semi.?abelian|generic.*graph|graph.*[Ff]inite` in `AlgebraicGeometry`:
   zero Mathlib hits.
4. `msearch.py ... leansearch`, query
   `finite fibres of scheme theoretic closure of generic semiabelian homomorphism graph`:
   eight hits on the scheme-fibre definition and finite morphism fibre results,
   all insufficient for this node's conclusion without a new theorem.
5. `rg -n` with the same concept pattern in `lean/WeilConjectures` and
   `lean/Sheaf`, followed by focused semiabelian-name searches: existing
   geometric-fibre definitions, power-integrality and trait-extension results,
   and the downstream normal-hom-extension theorem; no theorem for this node.
   `rg -n` for the exact node id in `lean/WeilConjectures` returned no hits.
6. Exact proposed declaration-name searches in Mathlib algebraic geometry,
   both project roots, and `dag/lean_names_upstream.json`: no collisions.
   API source searches located `Over.pullback`, its counit, `mapGrp`, and
   `Over.prodLeftIsoPullback`, which are reused rather than redefined.

Validation: `scompile.py Q94 lem-sfb-semiabelian-generic-graph-finite-fibres`
compiled the delivered module cleanly both as sandbox and under its actual
module name (3.3 and 3.2 seconds). An initial type error exposed that `uη.hom`
is still a monoid-object morphism; it was corrected to `uη.hom.hom`, the
underlying over-scheme morphism. The final file has explicit binders,
`set_option autoImplicit false`, no diagnostics, no lines over 100 characters,
and exactly one postponed theorem. No library or global build was run.

## Second reading by Q94

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
