## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleFramedLineEffectiveGluing` states
`AlgebraicGeometry.Scheme.etale_framed_line_effective_gluing`, with its proof `sorry`.
Two fully constructed helpers evaluate a transition unit on a test object and pull an
ordinary frame back using the canonical tensor composition and structure-unit maps.
There are no additional postponed theorems and no hollow definitions.

Source checked: `literature/stacks-project/descent.tex`, proposition-equivalence-quasi-coherent
(Tag 03DX), especially part (2) and the final two paragraphs of its proof; the effective
fpqc descent proposition (023T); lemma-equivalence-quasi-coherent-properties (05VG).
The final paragraph explicitly says the small etale case is proved in the same way.
No quasi-compactness or separatedness hypothesis occurs there.

Hypothesis and clause correspondence:

- A scheme and the size convention: `X : Scheme.{u}`, with explicit `universe u v` and
  both automatic-implicit options disabled. The section groups remain in universe u;
  the presented site has its usual object universe u+1. `I : Type v` is arbitrary.
- The small etale site is `X.Etale` with `X.smallEtaleTopology`. The structure ring is
  the existing `Modules.smallEtaleModuleRing X`, whose value is the actual regular
  function ring of each object, with pullback restrictions.
- The prescribed module is `G : ringedSiteModules.{u} (Modules.smallEtaleModuleRing X)`.
  This abbreviates Mathlib's category of module sheaves with all linear natural maps.
- The etale family is `U : I → X.Etale`. The hypothesis `hcover` says every point of X
  is the image of a point in some U a, exactly joint surjectivity; no finiteness or
  nonemptiness of I is assumed.
- Frames `t` are isomorphisms from the structure module to `G.over (U a)`. The slice
  `Over (U a)` is the localized small etale site, equivalent to the small etale site
  of `(U a).left`. Its objects `Over.mk f` retain the actual scheme and sections.
- Units `g a b` are units in the regular-function ring of `prod (U a) (U b)`. Products
  in X.Etale are scheme fibre products over X; this includes all repeated indices.
- `trfOverlapValue f h (g a b)` pulls back g along the unique map into that product.
  `hframes` is `t_b = t_a m_g` at every object of the overlap site and every function r.
  Factoring each test pair through the product makes this precisely equality of the
  overlap module maps, not merely equality at the final object.
- `hcocycle` states the triple-product cocycle after pullback to every test object
  with three maps. Taking the triple product recovers the original equation; pulling
  that equation back gives this formulation. `hdiag` is its separate normalization
  along the diagonal, using the pair of identity maps.
- The conclusion provides `L : X.Modules` and `hL : L.IsInvertible`, using the recorded
  ordinary Zariski-local rank-one definition. `lam a` is an isomorphism from the
  recorded tensor pullback along `(U a).hom` to the ordinary structure module.
- `trfPulledFrame L (lam a) f` first transports the structure arrow using `f.w`, then
  uses `tensorPullbackSectionComp`, the pullback of lam a, and the adjoint tensor-unit
  map. Its top-section map is exactly epsilon A(lam a) beta. No arbitrary comparison
  or unnormalized choice of natural isomorphism is an argument.
- The first conjunct asserts `lambda_a = m_g lambda_b` with these canonical pullback
  identifications, tested on every etale W and section. This is also equality of
  ordinary module maps on the overlap: etale test objects include all its Zariski opens.
- `etaleTensorSectionsSheaf L` is the recorded A_X(L), with quasi-coherence inferred
  from hL by the existing `IsInvertible.isQuasicoherent` theorem. The conclusion uses
  `∃! e` for an additive-sheaf isomorphism to the underlying additive sheaf of G and
  explicitly requires `e(r s) = r e(s)`. An additive natural isomorphism with these
  componentwise linearity equations is exactly a module-sheaf isomorphism. Its
  inverse is linear by applying the same equation to the inverse image of a section.
  No module action, section group, morphism, or restriction has been discarded.
- The second predicate conjunct identifies e with each specified local map on every
  object over U a. The third gives equality of the local maps on every overlap.
- The fourth is the explicit unique-amalgamation rule for e_W(s): for any y in G(W),
  its restrictions to W times_X U a have the displayed local values iff y = e_W(s).
  Restrictions of A_X(L) are the recorded `etaleTensorSectionsRestriction`.
- The fifth is the analogous rule for the inverse, using the actual inverses of
  t a and the pulled frame. These equivalences express existence and uniqueness
  of the section in each direction, including an empty covering family.
- Both e and its inverse are natural transformations of abelian sheaves, so they
  commute with every restriction and addition. The explicit scalar equation and
  invertibility give scalar compatibility in both directions. The local maps use
  actual module morphisms, and hence have these same compatibilities.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, `Scheme.Etale`;
  the jointly-surjective characterization is `ofArrows_mem_smallEtaleTopology_iff`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`.
- `WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`:
  `Scheme.Modules.IsInvertible.isQuasicoherent`.
- `WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf`:
  `Scheme.Modules.etaleTensorSectionsSheaf`; its recorded restrictions are public
  from `WeilConjectures.AlgebraicGeometry.EtaleTensorSections`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: `tensorPullback`,
  `tensorPullbackSectionComp`, and the section-normalized adjunction interface.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`:
  `tensorPullbackObjUnitToUnit` and `tensorPullbackObjUnitToUnit_isIso`.
  The latter proof is passed explicitly to Mathlib's `asIso`, fixing the actual map.
- `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`:
  `Scheme.Modules.smallEtaleModuleRing`. The existing definition node
  `def-sfb-scheme-zariski-etale-module-constructions` is added to stmt_deps;
  the equivalence theorem in the same module is not used as a hypothesis or chosen
  to construct A_X(L). Also add the landed node
  `lem-weil-pbc-module-pullback-structure-sheaf` for the specified unit comparison.
- Proof imports: `WeilConjectures.AlgebraicGeometry.Descent` (fpqc effectivity and
  invertibility descent) and `Sheaf.AlgebraicGeometry.FpqcFinerThanEtale`.
  `lem-trf-etale-line-sections-normalized-comparisons` has no recorded declaration
  in the current DAG; its future proof import is omitted. Its constructions needed
  for this statement are expressed directly from the existing canonical tensor
  comparisons and structure-unit map; no missing datum is assumed. The complete
  five-step proof remains in the theorem docstring.

Edge cases checked before finalizing: empty X and empty I (joint surjectivity forces
empty X, and the sheaf axiom makes the section characterizations unique); empty members
of a covering; repeated indices and diagonal normalizations; identity covers; arbitrary
infinite I; non-quasi-compact and non-separated schemes; zero regular-function rings on
empty objects. A zero G is not silently excluded: its proposed frames restrict which
covers can exist. No characteristic or nonzero-ring hypothesis is imposed.

Searches: the prescribed msearch.py leanfinder query "Effective descent of etale framed
line modules with transition units and unique sectionwise gluing" returned eight ring
etale API hits, none the assertion. Loogle `"SheafOfModules", "glue"` returned no hits.
Mathlib grep `etale.*[Mm]odule|[Ee]tale.*[Ss]tructure|framed.*[Gg]lu` returned seven
etale-ring/coefficient-module hits, none the assertion. Existing sandbox searches also
include LeanSearch "etale module sheaf descent with prescribed local frames" (eight
module-sheaf constructors/local generators, no effective gluing) and Loogle
`"SheafOfModules", "descent"` (no hits); exact outputs are in searches.jsonl.
The project searches used rg on both lean/WeilConjectures and lean/Sheaf for framed,
normalized comparisons, etale structure rings, and tensor-section modules; the exact
item-id search had no matching declaration. They found the already-recorded additive
section sheaf, smallEtaleModuleRing, and tensor-unit map, which are reused. A broader
existing comparison module was inspected, but its equivalence statement does not give
the prescribed-frame, cocycle, or unique sectionwise assertion and is not imported.
The two helper names and main theorem name have no upstream/project name collisions.

No mathematical statement correction and no STATEMENT-DISPUTED flag. Only lean and the
two additional landed statement dependencies change in the item JSON.

## Second reading by Q131

Single-worker rereading of the node and full Lean file; the dispatch forbids starting
another agent and assigns independent review to the maintainer. This is not represented
as an independent agent's review.

The reread checked all seven original statement dependencies and each hypothesis and
conclusion listed above. It found and repaired a dependency-cycle risk in the draft:
the broader `scheme_etale_invertible_comparison` module belongs to a citer of this
item, so it is not imported. Its temporary structure-ring, section-sheaf and unit-map
references were replaced by existing foundational declarations: smallEtaleModuleRing,
etaleTensorSectionsSheaf, and tensorPullbackObjUnitToUnit. The ring-construction and
unit-comparison nodes are cited explicitly. The current statement uses no equivalence
witness or arbitrary local comparison. The reread also checked the transition sign:
frames satisfy t_b = t_a m_g while ordinary lambda_a = m_g lambda_b; consequently the
local maps agree. Both unique-amalgamation equivalences include every test object W,
and inverse compatibility is retained. Naturality/additivity are carried by the actual
abelian-sheaf isomorphism, and scalar linearity is explicit. Casts by `@id` only expose
definitionally identical section types for instance synthesis. Every binder and universe
is explicit. The ordinary pullback is tensorPullback throughout. The source statement,
including arbitrary covers and the absence of finiteness/separatedness assumptions,
is unchanged.
