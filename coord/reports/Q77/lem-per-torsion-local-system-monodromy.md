## Worker report

The delivery states `AlgebraicGeometry.Scheme.torsion_local_system_monodromy` in
`Sheaf.AlgebraicGeometry.TorsionLocalSystemMonodromy`. Its only postponed proof is this
named theorem, with all thirteen proof steps in its docstring. The added definition module
contains real data only. No source or target statement was changed.

Source read: ILO, Travaux de Gabber, Exposé XVII, Definition 7.2.1, Propositions 7.2.2–7.2.5,
and Lemma 7.2.6, printed pp. 301–303 (PDF pp. 307–309), including Exercise 7.2.7. The
exercise explains why étale local constancy alone is the wrong predicate here.

Hypothesis and clause correspondence:

* `S : Scheme.{u}`, `[IsNoetherian S]`, and `[ConnectedSpace S]` give exactly a nonempty
  connected Noetherian scheme. ConnectedSpace includes Nonempty. The ambient closure
  clauses quantify over all Noetherian schemes, including the empty scheme.
* `(Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)` is the geometric point.
* The group is `Aut (FiniteEtale.fiber s)` with Mathlib's evaluation topology. This is the
  existing finite-etale presentation of the group in def-galois-fibre-functor. The
  finite-etale/FLC equivalence identifies it canonically with `Aut (flcFiber s)`; the
  project explicitly permits this presentation in FundamentalGroup.Basic. No abstract
  group, finite quotient, arbitrary action or extra group hypothesis is substituted.
* `(R : Type (u + 1)) [CommRing R]`, `(n : ℕ)`, `hn : 0 < n`, and `hR : (n : R) = 0`
  give exactly the torsion coefficient hypothesis. There is no finite-ring assumption.
* Ambient objects are `Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} R)`, the established
  constructible-sheaf encoding of modules over the constant ring sheaf. Its scalar maps
  are R-linear; local constant scalars act by gluing the fixed scalar operations. This
  is the project's existing encoding, used by the recorded finite-type and stalk nodes.
* `IsIndFiniteEtaleSheaf` uses an actual small filtered diagram `D : I ⥤ S.FiniteEtale`,
  its represented sheaf diagram, a colimit cocone, and an isomorphism to the given sheaf.
  `IsIndFiniteEtaleModule` applies this to the existing underlying-set sheaf functor.
  `IndFiniteEtaleModules` is the full subcategory, retaining all ambient morphisms.
* The already recorded `Rep.DiscreteContinuousRep` gives arbitrary R-modules with
  R-linear G-actions and open stabilizer of every element, and equivariant linear maps.
* `TorsionLocalSystemStalkEquivalence.equivalence`, `.additive`, and `.stalkIso` state the
  additive equivalence with underlying functor naturally the actual geometric stalk.
  `.finiteGerm` pins the canonical action: a germ of a section over a finite étale P at
  a is carried to its germ at g(a). This prevents a twisted abstract equivalence.
* The first conjunct after the existential family E compares ambient `ShortExact` with
  injectivity, `Function.Exact`, and surjectivity of the two underlying stalk linear maps.
  This is preservation and reflection of short exact sequences in the precise ambient
  senses required. A categorical ShortComplex.map-to-stalk expression initially left an
  unresolved universe metavariable; the explicit underlying-module expression compiles
  and is precisely the node's assertion, without restricting the site universes.
* The constants clause says `L.obj.IsConstant ↔ ∀ g x, ρ g x = x`; the separate clause
  makes every constant sheaf a local system, including constants of infinite modules.
* `IsFiniteLocallyConstantSheaf L.obj ↔ Module.Finite R (stalk L)` is the final
  finite-type criterion, using the predicate explicitly exposed by the recorded
  def-weil-pbc-locally-constant-finite-type-modules. Its meaning is local constancy with
  finitely generated stalks, not finite underlying sets.
* A finitely generated stalk implies `∃ P : S.FiniteEtale, IsGalois P ∧ ...IsConstant`.
  IsGalois is the recorded intrinsic Galois predicate; it includes connectedness and
  corresponds to simply transitive cover automorphisms on the fibre.
* For a connected finite étale `c : T ⟶ S`, h is continuous, injective, and has open range.
  Its equation on finite-cover fibres characterizes the canonical c_*; it is not an
  unconstrained map. The equation with `upperStarCompSheafFiberIso` says that the canonical
  stalk comparison intertwines the pullback action with ρ(h(g)). The following iff says
  exactly that the pullback is constant iff the image subgroup acts trivially.
* The next clause gives ambient `kernel f.hom` and `cokernel f.hom` as local systems.
* The ambient ShortComplex clause says an extension with local-system first and last
  terms has local-system middle term; it does not assume the middle term local.
* For every `I : Type (u + 1)` with SmallCategory, every ambient diagram and every
  colimit cocone c whose terms are local systems, c.pt is local and the actual stalk
  sends c to a colimit cocone. The index need not be filtered or nonempty. Thus the
  inclusion and stalk commute with all small colimits, not just filtered colimits.
* Finite-cover descent quantifies over an arbitrary ambient L and only assumes that
  `c⁻¹L` is local; L need not be local beforehand. Connectedness of T rules out the empty
  non-surjective cover. No surjectivity hypothesis was added; it follows here.
* `torsionLocalSystemComponent S x` uses the existing openness theorem to give the open
  connected component through x. The last iff tests local systems on these components.
  Together with all the closure clauses on arbitrary Noetherian S and the connected
  monodromy clauses, this renders the assertions component by component. Repeated x in
  the same component changes no condition. For empty S the test is vacuous.

Dependency interfaces read and used:

* Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and scheme morphisms;
  Mathlib.Topology.Connected.Basic: `ConnectedSpace`; Mathlib.AlgebraicGeometry.Noetherian:
  `IsNoetherian`; Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing`.
* Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber: `Scheme.flcFiber`;
  WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale: `FiniteEtale.fiber`;
  Mathlib.CategoryTheory.Galois.Topology: the topology on its automorphisms;
  FundamentalGroup.Restriction: `FiniteEtale.pullbackFiberIso`.
* Mathlib.AlgebraicGeometry.Sites.Etale: `smallEtaleTopology`;
  Sheaf.CategoryTheory.RingedSiteModules: `ringedSiteModules` and the documented
  SheafOfModules interface; Mathlib.CategoryTheory.Sites.ConstantSheaf: `constantSheaf`;
  Mathlib.CategoryTheory.Limits.HasLimits: `Cocone`, `IsColimit` and colimits;
  Mathlib.CategoryTheory.Filtered.Basic: `IsFiltered`.
* Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules exposes upstream
  `IsFiniteLocallyConstantSheaf`, `IsFiniteSheaf`, and `IsLocallyConstantSheaf`;
  Mathlib.RingTheory.Finiteness.Defs: `Module.Finite`;
  Mathlib.CategoryTheory.Galois.GaloisObjects: `PreGaloisCategory.IsGalois`.
* Sheaf.AlgebraicGeometry.PointedEtaleStalk: `pointedEtaleStalk` and its diagram;
  the module-valued specialization is the same colimit already supplied by
  `(pointSmallEtale s).sheafFiber`. Geometric points use IsAlgClosed and Spec as recorded.
* WeilConjectures.RepresentationTheory.DiscreteContinuousRep:
  `Rep.DiscreteContinuousRep` (def-exc-discrete-modules-category, now cited).
* WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk:
  `Etale.upperStarCompSheafFiberIso`; the pullback itself is `Etale.upperStar`.
* WeilConjectures.Mathlib.Topology.NoetherianSpace:
  `TopologicalSpace.NoetherianSpace.isOpen_connectedComponent`.

Every recorded proof-dependency module is imported without `public` unless already a
public statement dependency. The following proof dependencies have no published declaration
and hence no module to import: lem-per-torsion-torsor-descent,
lem-weil-pbc-filtered-colimits-commute-finite-limits, and
lem-weil-pbc-site-sheaf-sets-limits-sectionwise. They are used only in the proof plan,
not to supply data in any definition. No import cycle is introduced.

Edge cases checked: R=0 (including n=1); arbitrary nonminimal positive annihilator;
constants with value F_p[t]; infinite direct sums of F_p; zero modules and the empty
finite étale representative; empty diagram colimits; nonempty singleton filtered indices;
the empty base in all disconnected clauses; disconnected finite clopen decompositions;
identity finite cover; a non-Galois connected cover (only the finite-generation conclusion
asks for Galois); infinitely generated stalks having no common finite trivializing cover.
The finite subgroup proof uses additive Z/n-subgroups, never finite R-submodules.
No statement fault or STATEMENT-DISPUTED issue was found.

Searches actually run through msearch.py: leanfinder, "torsion etale local systems
equivalence discrete continuous fundamental group modules" returned condensed-discrete
constructions, not this theorem; loogle "ContAction, ModuleCat" returned no hits;
grep "LocalSystem|localSystem|IndFinite" in AlgebraicGeometry returned no hits. For the
new predicate, leansearch and leanfinder "filtered colimit of finite etale representable
sheaves ind finite local system definition" returned generic IndObjectPresentation,
filtered sheaf colimits, condensed constructions and finite presentation predicates;
grep "IsIndFinite|IndFiniteEtale|IsLocalSystem" in AlgebraicGeometry returned zero hits.
Direct rg in upstream WeilConjectures and lean/Sheaf found finite local systems and ordinary
local constancy but no ind-finite predicate. Searching the DAG and blueprint for local
systems and filtered colimits found this item's text and its consumers, not an existing
ind-finite definition node. The discrete representation category was found and reused.

Validation: prescribed scompile.py on both modules in dependency order, no errors or
warnings; main file about 15–17 seconds and definition file about 2 seconds, under 60 seconds.

## New nodes

`def-per-ind-finite-etale-local-system` defines precisely ILO XVII Definition 7.2.1 and
its module variant, using actual representable sheaves and colimit universal properties.
It has its own module, IsIndFiniteEtaleSheaf, IsIndFiniteEtaleModule and full subcategory.
The searches above found no existing notion; ordinary locally constant sheaves are not
substituted. Its source, ancestor, via chain and searches are recorded in the node.

## Second reading by Q77

This is a separate clause-by-clause self-audit, not a claim of an independent agent review:
the dispatcher explicitly forbids starting other agents and provides independent maintainer
review of the delivery. I reopened the source, node and final files. I checked the order and
scope of every conjunction: the single existential family E governs exactness, constants,
finite generation and all finite-cover comparisons; ambient closure, extensions, colimits,
constants, descent and component testing are outside that family and include disconnected S.
The short-exactness target is parenthesized as an iff to the conjunction of injective,
exact and surjective, all on the actual module-valued stalk maps. The cover map h is pinned
on every finite-cover fibre, and the module pullback comparison uses the existing canonical
stalk isomorphism. The finite-germ equation uses the forward action g(a), agreeing with the
finite-etale fibre evaluation action. No missing clause, extra finiteness hypothesis, hollow
data or hidden auto-implicit was found. The compile repairs only changed explicit universe
annotations, exactness presentation, imports and line wrapping, not mathematical hypotheses.
