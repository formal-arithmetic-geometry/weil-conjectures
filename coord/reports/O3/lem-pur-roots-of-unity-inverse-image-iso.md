## Worker report

The delivery states all three clauses of `lem-pur-roots-of-unity-inverse-image-iso`
in `Sheaf.AlgebraicGeometry.RootsOfUnityInverseImageIso`. It also supplies the two genuine
unstated prerequisite nodes in their own modules, as authorized by the human's
2026-10-16 “Unstated dependencies are yours to state” instruction. Every theorem has
proof `by sorry`; every definition has actual data, or selects the uniquely determined
object of an explicitly normalized existence-and-uniqueness theorem. No statement is
corrected, no hypothesis is added, and no new DAG node is introduced.

Hypothesis and clause correspondence for the item:

- Schemes and the arbitrary scheme morphism are `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  The site is Mathlib's `Scheme.ProEt.topology`, with objects in universe `u+1` and
  morphisms in universe `u`; abelian groups and coefficient rings are in universe `u+1`.
  No universe equality, quasi-compactness, Noetherian, characteristic or invertibility
  hypothesis is imposed.
- The positive integer `N` is `N : ℕ` with `hN : 0 < N`, wherever its module action or
  a transition requires positivity. The definition of the sheaf and its comparison
  extends to all natural exponents, consistently with the recorded roots sheaf.
- The maps `c^f_{mu_N}` are `proEtaleRootsOfUnityInverseImageMap f N`, defined in the
  supplied prerequisite module as the adjunct of the projection pullback on roots.
  The coefficient map is the recorded `proEtaleConstantInverseImageMap f RingCat`
  applied to `RingCat.of (ULift (ZMod N))`. Its source is exactly the inverse image of
  the recorded `proEtaleRootsOfUnityCoefficientRing Y N`.
- Clause 1 is the first conjunct of `proEtaleRootsOfUnityInverseImageIso`, quantified
  over `N N'`, both positivity proofs, and `h : N ∣ N'`. Composition uses Lean's
  left-to-right `≫`, so the equation is `f⁻¹(t_Y) ≫ c_N = c_N' ≫ t_X`, exactly the
  node's square. The transition is the dependency's kernel-induced power map, rather
  than a map of constant sheaves.
- The consequence for every prime `ℓ` is the second conjunct. It supplies a natural
  transformation from `proEtaleRootsOfUnityTower Y ℓ hℓ ⋙ f⁻¹` to the corresponding
  tower on `X`, with component `c_(ℓ^(r+1))` at every `op r`. Thus `r : ℕ` encodes
  every original positive tower index and the first level is `mu_ℓ`.
- Clause 2 is the third conjunct, quantified over positive `N`, every object `U`,
  every scalar `a` in the inverse-image ring, and every root section `x` in the
  inverse-image abelian sheaf. It states the exact scalar identity using explicit
  `SMul.smul` calls. The target action is the dependency's
  `torsionSheafModuleStructure` from `proEtaleRootsOfUnityModule`. The source action
  is the induced action on the *same fixed* inverse-image ring and abelian sheaf,
  supplied by `proEtaleRootsOfUnityInverseImageAction`. Its normalization on the
  actual ring and additive adjunction units, and compatibility with restrictions,
  uniquely characterize the action obtained by applying inverse image to scalar
  multiplication. In particular `a` is not restricted to a constant section.
- Clause 3 is the fourth conjunct. It quantifies over the isomorphism hypothesis
  `IsIso f` and every positive `N`, asserting `IsIso` of the actual comparison map.
  Its second part states the identity on roots of global sections at *every* `U`.
  Both sides use the dependency's `proEtaleRootsOfUnitySections`; the right side
  first applies the supplied canonical site identification. Postcomposition changes
  only the structure map, so both resulting root subgroups are definitionally the
  roots of the identical global-sections ring of the underlying scheme of `U`.
  This includes the canonical normalization, not merely existence of some isomorphism.

The auxiliary action interface belongs to this comparison's scalar-compatibility clause.
`IsProEtaleRootsOfUnityInverseImageAction` gives the normalization and restriction
conditions explicitly. `existsUnique_proEtaleRootsOfUnityInverseImageAction` supplies
and uniquely determines its data by the finite-product-preserving inverse-image
construction. Its proof docstring explains preservation of the module identities and
uniqueness from the Kan-extension generators and local sheafification generators.
The selected module structure is marked `@[instance_reducible]`; no file-local
instance, private abbreviation, notation or theorem proof is used.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`:
  `AlgebraicGeometry.Scheme.proEtaleRootsOfUnitySheaf`, `proEtaleRootsOfUnitySections`,
  `proEtaleRootsOfUnityCoefficientRing`, `proEtaleRootsOfUnity_nsmul`,
  `proEtaleRootsOfUnityTransition`, and `proEtaleRootsOfUnityTower`.
  These are the recorded declarations, including their additive and universe-lift
  conventions, rather than the upstream small-etale sheaves.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `AlgebraicGeometry.Scheme.proEtaleBaseChange`, `proEtaleSheafInverseImage`,
  `proEtaleSheafDirectImage`, `proEtaleSheafAdjunction`, and
  `proEtaleConstantInverseImageMap`. The ring and additive units in the helper are
  those of these very adjunctions.
- `Sheaf.CategoryTheory.TorsionSheafConstantModule`:
  `CategoryTheory.constantZModRingSheaf`, `torsionSheafModuleStructure`, and the
  uniquely normalized module structure and additive-morphism linearity statements.
- `Sheaf.AlgebraicGeometry.ProEtaleStructureSheaf`:
  `AlgebraicGeometry.Scheme.proEtaleStructureSheaf`, the actual global-sections ring
  with restriction maps. It is used via the root-section equivalence and the
  fibre-product projection's `Scheme.Hom.appTop`.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules` is exactly Mathlib's `SheafOfModules`; the
  prerequisite's module equivalence uses this recorded category.
- `Sheaf.AlgebraicGeometry.ProEtaleOperations`:
  `proEtaleRingModulePullback` and `proEtaleRingModuleDirectImage` specialize the
  recorded inverse-image action, actual sheaf tensor extension and direct image.
  They supply the already existing functors for the prerequisite's constant-module
  clause. Their coefficient isomorphism has hom exactly the recorded constant map.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `limit`, `limit.π`, and `limit.post`.
  The latter is the map induced by the inverse images of the limit projections.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`,
  and `sheafificationAdjunction`. The proof-dependency modules
  `ProEtaleConstantRingMap`, `TorsionSheafConstantModule`, `RingedSiteModules`,
  `ProEtaleStructureSheaf` and `Sheafification` are imported directly for stage 3.
- `def-weil-scheme-morphism-properties` is explicitly a convention node with no own
  declaration. Its scheme and morphism notions here are the ordinary Mathlib ones.

Edge cases checked: `N=1` (the trivial root sheaf and zero coefficient ring), the
empty scheme and empty site object (the zero ring and its trivial unit group),
noninvertible `N`, residue characteristic dividing `N`, the identity scheme map,
an arbitrary scheme isomorphism, the first prime-power level, equal exponents
`N=N'`, and nonconstant local scalar sections. There is no `N=0` assertion about
module structures or transitions; the underlying comparison definition harmlessly
extends to zero, as does the recorded sheaf definition. No generator of roots is
chosen. The two fibre-product factors in the existing site convention are reversed
from the node's display: `pullback.fst V.hom f` is the projection to `V` and the
map/pullback adjunction unit is `(id_U,u)`. This is exactly `(u,id_U)` for the node's
factor order and yields the same identity-on-sections normalization.

Searches made:

- `msearch.py`, LeanFinder: “The inverse image comparison of proetale roots of unity
  commutes with power transition maps and is semilinear”. Eight hits concern
  cyclotomic characters or perfection maps, not this statement or pro-etale sheaves.
- `msearch.py`, Loogle: `rootsOfUnity, MonoidHom`. Twelve hits include
  `restrictRootsOfUnity` and `map_rootsOfUnity`. These concern roots in individual
  rings. `restrictRootsOfUnity` is used in the prerequisite's exact projection
  formula; none supplies the sheaf comparison or its compatibilities.
- `msearch.py`, grep: `rootsOfUnity|proEtaleRootsOfUnityInverse` in Mathlib's
  `CategoryTheory` directory: no hits.
- `msearch.py`, LeanSearch: “A scheme isomorphism induces an equivalence on proetale
  sheaves with inverse image computed by composition of structure maps”. The service
  returned Internal Server Error; it is recorded unavailable, not a negative result.
- `rg` in Mathlib, upstream `WeilConjectures`, the supplied framework and `lean/Sheaf`
  found the already landed pro-etale roots construction, which is reused, and the
  upstream `RootsOfUnityPullback`/`Kummer` modules for the *small etale* site.
  The latter have different sites and additional invertibility hypotheses for their
  isomorphism statements, so they do not state the present node. The
  `PurityAffineLineDatum.rootPullback` interface likewise concerns etale roots at
  one fixed exponent. No equivalent pro-etale comparison declaration was found.
  A further name search against `dag/lean_names_upstream.json`, Mathlib, upstream
  sources and `lean/Sheaf` found no collision for any new declaration.
- `scompile.py --source Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage`
  and `... ProEtaleIsomorphismInverseImage` confirmed that no published module of
  either expected name existed. Read-only inspection of delivery branches found
  `deliver/NB/def-pur-roots-of-unity-inverse-image` and
  `deliver/Q35/lem-weil-proetale-isomorphism-inverse-image`; both dependency node
  records still have `lean: null`, so these are not usable Lean deliveries.

Sources read: Stacks `etale-cohomology.tex`, section-kummer (Tag 03PK), explicitly
introduces the roots functor on all schemes and notes fpqc descent; Stacks
`proetale.tex`, section-morphism (Tag 09A5), defines the base-change-induced site
morphism for an arbitrary scheme map. Deligne, Weil I, printed pp. 280--281,
§2.2, gives the power-transition root system. The adjunction and uniqueness
arguments are the elementary constructions spelled out in the item's proof.
The supporting declarations each have source/blueprint docstrings and complete
natural-language proof plans. No `STATEMENT-DISPUTED` fault remains.

Validation: all three delivered modules compile separately in dependency order
through `scompile.py` with the published overlay, at the prescribed 60-second
per-file limit. The initial class-reducibility warning was repaired by the
instance-reducible attribute. All variables and universes are bound explicitly
and `autoImplicit` is false. The first dry run found only the missing independent second-reading section and a
metadata mismatch: the preflight signature parser starts at `def`, omitting
`noncomputable`. The dependency record was corrected accordingly and the required
dry run was repeated. The worker does not write the second reader’s section.

## Dependency modules

`def-pur-roots-of-unity-inverse-image` had neither a `lean` record nor a Mathlib
match. `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage` states the
existence and uniqueness of its direct-image root map using the exact
`restrictRootsOfUnity (pullback.fst V.hom f).appTop.hom N` formula at every section.
It selects that uniquely characterized map and defines its adjunct using
`proEtaleSheafAdjunction`. This is exactly the source construction of beta and c,
without introducing arbitrary replacement data. Only the dependency's `lean`
field changes, with the required explanatory note.

`lem-weil-proetale-isomorphism-inverse-image` had neither a `lean` record nor a
Mathlib match. `Sheaf.AlgebraicGeometry.ProEtaleIsomorphismInverseImage` supplies
postcomposition of structure maps and states that it is a covering-preserving
equivalence with postcomposition by `inv f` as a quasi-inverse. The canonical
section identification is selected from an existence-and-uniqueness statement
whose inverse is fixed by the actual adjunction unit and distinguished comma
arrow; it is natural in both the sheaf and the object. Further declarations
state invertibility of the recorded inverse-image adjunction unit and counit,
preservation of all small limits and colimits, the canonical inverse-system
comparison `limit.post`, the constant coefficient comparison and its naturality,
and the equivalence on modules over every constant commutative coefficient
ring. Thus clauses 1, 2 (including exactness by preservation of finite limits
and colimits), and 3 of this dependency are all present. The generic coefficient
category includes sets, abelian groups and rings; for modules the separate
statement uses the recorded ringed-site module functors. Only the dependency's
`lean` field changes, with the required explanatory note.


## Second reading by N3

Independent second reader, 2026-10-16. I opened the item and both dependency
nodes, all three sandbox modules, and the recorded dependency sources in the
read-only shared checkout. I read Deligne, Weil I, printed pp. 280--281,
§2.2, and the local Stacks TeX: `etale-cohomology.tex`, section-kummer
(Tag 03PK), `proetale.tex`, section-morphism (Tag 09A5), and `sites.tex`,
lemma-adjoint-sheaves (Tag 00WX) and the proposition on functoriality of
algebraic structures (Tag 00YV). The Stacks roots functor and site morphism
are introduced for arbitrary schemes. Invertibility of the exponent occurs
in the subsequent Kummer exactness lemma, not in the roots functor. Deligne
supplies the positive prime-power tower and power transitions; the node
explicitly supplies the general-scheme comparison calculations.

My object/hypothesis/conclusion checklist and Lean correspondence:

1. Arbitrary schemes X and Y and a morphism f: `{X Y : Scheme.{u}}`
   and `(f : X ⟶ Y)`. Verdict: exact; no field, finiteness, separatedness,
   Noetherian, characteristic, or invertibility hypothesis appears.
2. Their small pro-etale sites: `ProEt.topology X` and `ProEt.topology Y`.
   I read `proEtaleBaseChange`, `proEtaleSheafDirectImage`,
   `proEtaleSheafInverseImage`, and `proEtaleSheafAdjunction` in the recorded
   `ProEtaleInverseImage` module. These are the actual base-change site
   functor and its sheaf adjunction, with objects in universe u+1 and
   morphisms in u. Verdict: the correct sites and functors.
3. Positive exponents N and N': `(N N' : ℕ)` and `hN : 0 < N`,
   `hN' : 0 < N'`. The dependency's root sheaf is the kernel of
   `N • 𝟙` on the actual units sheaf, with `proEtaleRootsOfUnitySections`
   normalized by its inclusion. Verdict: genuine roots of the global
   sections ring, rather than a constant sheaf or chosen cyclic group.
4. The canonical comparison c: `proEtaleRootsOfUnityInverseImageMap f N`.
   The supplied prerequisite defines it by the recorded adjunction's
   `homEquiv.symm` from beta. Beta is uniquely fixed at every V by
   `restrictRootsOfUnity (pullback.fst V.unop.hom f).appTop.hom N` under
   the recorded root-section equivalences. Verdict: exact projection
   pullback, with no arbitrary morphism. The variable factor comes first
   in the dependency's fibre product, explaining `fst` instead of `snd`.
5. The coefficient ring and coefficient comparison: the recorded
   `proEtaleRootsOfUnityCoefficientRing`, transparently
   `constantZModRingSheaf`, and `proEtaleConstantInverseImageMap f RingCat`
   at `RingCat.of (ULift (ZMod N))`. Verdict: the same constant Z/N ring
   and the same canonical comparison as in the node; ULift changes size
   only and uses the fixed u+1 coefficient universe.
6. Divisibility and transition square: `h : N ∣ N'` and the first
   conjunct of `proEtaleRootsOfUnityInverseImageIso`. I read the recorded
   `proEtaleRootsOfUnityTransition`, which is the kernel lift of the
   `(N'/N)`-power map on units. In Lean's composition order the equality
   is `f⁻¹(t_Y) ≫ c_N = c_N' ≫ t_X`. Verdict: exactly the node's square,
   with all exponents positive and with the actual root transitions.
7. The prime-power consequence: the second conjunct quantifies over
   `(ℓ : ℕ) (hℓ : ℓ.Prime)` and supplies a natural transformation of the
   two `proEtaleRootsOfUnityTower` diagrams. Its components are fixed to
   `c_(ℓ^(r+1))` at every `op r`. I read `Functor.ofOpSequence` in the
   tower definition. Verdict: all positive indices, beginning with μ_ℓ,
   and naturality for the inverse-system transitions, with no level lost.
8. Semilinearity: the third conjunct quantifies over every site object U,
   every local section a of the inverse-image ring and every local section
   x of the inverse-image root sheaf. Its equality uses precisely these
   sectionwise maps. The target action is the recorded
   `torsionSheafModuleStructure` used by `proEtaleRootsOfUnityModule`.
   The source action is uniquely fixed on the same underlying ring and
   abelian sheaf by compatibility with the actual ring and group
   adjunction units and by restriction compatibility. Verdict: the
   inverse-image action, and the assertion covers nonconstant local a.
   Unit sections and their restrictions generate the Kan extension and
   locally generate its sheafification, so this uniqueness condition
   determines the action; it is not an arbitrary module structure.
9. The scheme-isomorphism hypothesis: the final conjunct quantifies over
   `_hf : IsIso f`, then all positive N. Verdict: an implication under
   precisely the node's extra hypothesis, not a restriction of clauses
   1 or 2. `IsIso (proEtaleRootsOfUnityInverseImageMap f N)` gives the
   requested abelian-sheaf isomorphism.
10. Canonical identity on roots: the same final conjunct compares both
    sides through `proEtaleRootsOfUnitySections`, with the right side
    evaluated at `(proEtaleIsoPostcompose f).op.obj U` after
    `proEtaleIsoInverseImageIdentification`. I read its normalization:
    the inverse is the actual adjunction unit followed by restriction
    along `proEtaleIsoCommaArrow`, the map/pullback adjunction unit.
    Postcomposition retains the underlying scheme and global-sections
    ring. Verdict: equality of the same roots at every U, precisely the
    identity under the specified identification, not merely an unspecified
    isomorphism.

Dependency-module reading (H13):

- `def-pur-roots-of-unity-inverse-image`: the source's beta formula,
  naturality and additive nature are the uniquely normalized direct-image
  map theorem; c is its actual adjoint. The real map is determined by the
  projection formula, so choosing its unique witness is not a hollow
  definition. The harmless definition for N=0 adds no hypothesis to the
  node's positive-exponent use. The dependency node changes only in lean.
- `lem-weil-proetale-isomorphism-inverse-image`: postcomposition and its
  inverse preserve coverings and are quasi-inverses; the normalized
  natural section identification supplies clause 1. The generic
  equivalence theorem supplies clause 2 for sets, groups and rings,
  with invertible actual unit and counit and preservation of all small
  limits and colimits (hence exactness in the abelian cases). The
  `limit.post` theorem is the canonical comparison of inverse-system
  limits. The constant comparison and naturality supply clause 3.
  The existing module theorem uses the recorded ringed-site module
  pullback/direct image and supplies clause 2 for commutative constants.
  **Mismatch found:** the node also permits module sheaves over a
  noncommutative constant ring, while the explicit module theorem took
  only `CommRingCat`. I added
  `proEtaleIso_constantRingModuleEquivalence` for `A : RingCat.{u+1}`.
  Its two categories are the recorded `ringedSiteModules`, and its inverse
  functor is required to equal Mathlib's actual `SheafOfModules.pushforward`
  along `proEtaleBaseChange f`, with scalar restriction through the
  recorded `proEtaleConstantDirectImageMap`. Thus this is the equivalence
  with the specified direct image; its forward functor is the inverse
  image determined by the adjunction, without a commutativity assumption.
  The theorem has a source/blueprint docstring and a full transport proof
  plan, and its proof is only sorry. I added its name to lean.declarations
  and explained the repair in lean.note. No definition is selected from
  this existential statement. All other dependency content is retained.

Edge cases checked independently: N=1 gives the trivial root group and
zero coefficient ring; the source action exists on the trivial group.
N=0 is excluded exactly where the node requires positivity; only the
underlying root/comparison definitions extend to it. No hypothesis excludes
residue characteristic dividing N or a nonreduced scheme. The empty scheme
and empty test object have the one-element units group of their zero ring;
all displayed maps and identities still make sense. N=N' gives the
identity-power transition. The tower begins at r=0 in Lean, corresponding
to original r=1, and requires only primality, not invertibility on X.
Identity maps and arbitrary scheme isomorphisms use the same normalized
comma arrow. The noncommutative module repair includes the zero ring.
The arbitrary universes u, v, w and w' are bound: the generic value category
has the existing inverse-image API's Hom universe u+1, which includes sets,
abelian groups and rings in the common size convention. No extra equality
of the site's object and morphism universes is introduced.

Independent searches (H4):

- LeanFinder through msearch.py: “The pullback map on torsion unit group
  sheaves is compatible with power maps and is identity after transport
  along an isomorphism”. Eight hits, about Selmer groups, units and module
  pullbacks; none states the pro-etale comparison. A further query on
  noncommutative constant-ring module sheaves found general site transport
  and `SheafOfModules.pushforwardCongr`, not this scheme/site statement.
- Loogle through msearch.py: `"restrictRootsOfUnity"`. Five hits give
  restriction of monoid homomorphisms and equivalences to roots of unity;
  these justify the ring-level construction but do not supply its sheaf
  comparison or the theorem. The dependency already uses the exact
  `restrictRootsOfUnity` declaration.
- LeanSearch through msearch.py: “Inverse image of roots of unity sheaves
  commutes with power maps”. Internal Server Error; recorded unavailable,
  not as a negative result.
- Independent rg of Mathlib, the slopmaster2 WeilConjectures source, the
  shared Sheaf library and the published framework used roots, torsion
  units, power/pullback and rootPullback terminology. I opened
  `RootsOfUnityPullback`, `GmTransport`, and `PurityAffineLineDatum`.
  Their roots statements use `Etale.upperStar`, `smallEtaleTopology`,
  or a fixed purity exponent; the unrestricted pro-etale statement is not
  present. I also checked all delivered names against the upstream name
  index and searched the new general-ring theorem name: no collision.
  The established general `SheafOfModules` and ring/module pushforward
  constructions are reused, not copied.

No new definition nodes and no statement_change are needed. The main
item's mathematical statement and all its Lean clauses remain unchanged.
All three node copies differ from their shared counterparts only in lean;
their lean.statement strings occur verbatim as their source signatures.
Every definition has real data or takes the unique normalized witness of a
named theorem; every postponed theorem has its owning blueprint tag and
source/proof docstring. No proof was filled, and no file-local notation,
instance or private definition was introduced.

Additional interface check: I opened the existing
`SheafOfModules.AlgebraicInverseImage` and
`AlgebraicInverseImageOfUniverses`. These are input structures carrying
arbitrary ring/module lift functors and underlying-set comparison data;
they do not construct the normalized action on the specific, already fixed
RingCat and AddCommGrpCat inverse images used here. The specialized
unit-normalized action does not replace either general structure. The
recorded `proEtaleModuleInverseImage` also returns modules on the inverse
image in CommRingCat, rather than a module structure on the fixed independent
RingCat/abelian inverse images; the current normalization addresses exactly
that interface without changing those underlying sheaves.

Validation after the second-reader repair: all three delivered files passed
`scompile.py` separately in the private overlay, including both preliminary
sibling compiles and their individual library compiles. The final module
times were 4.5 s, 6.0 s and 10.5 s, below the unchanged 60-second limit.
There were no errors or warnings. No global build or direct git command
was run. The first compile invocation used relative paths from the shared
checkout and found no sandbox files; it was immediately corrected to the
absolute sandbox paths, and both complete compilation passes succeeded.
