## Worker report

The delivery states `CategoryTheory.siteConstantModule_isomSheaf` in
`Sheaf.CategoryTheory.SiteConstantModuleIsomSheaf`, with its entire proof `sorry`.
It also constructs the constant-module functor over the constant ring sheaf, using
Mathlib's existing module-sheafification functor. No mathematical claim is proved.
The supplied structure laws in the definition are definitional identities; there
is no postponed data or `sorry` in either definition.

The node and its statement are unchanged, except that `stmt_deps` gains the new
definition node below. No statement correction, unusable dependency, or disputed
statement was found. Stacks Modules on Sites, Tag 093T(2), is exactly the claimed
comparison; its proof uses the finite-presentation Hom comparison and inverse pairs.
I read the local source `sites-modules.tex`, lemma-locally-constant, and the complete
four-step proof in the DAG node.

Clause-by-clause rendering:

- A small site is `{C : Type u} [SmallCategory C] (J : Precoverage C)` with
  `[J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange]
  `[J.HasPullbacks]`, exactly the recorded convention of
  `def-weil-pbc-sites-and-cohomology`. Sheaves use `J.toGrothendieck`.
- The coefficient ring is `(Λ : Type u) [CommRing Λ]`. No nonzero-ring,
  noetherian, characteristic, finite-ring, or connectedness assumption occurs.
- The two modules are `(M N : ModuleCat.{u} Λ)`, with separate
  `[Module.FinitePresentation Λ M]` and `[Module.FinitePresentation Λ N]`.
  Mathlib defines finite presentation by finite generators with finitely generated
  relation kernel, equivalent over a ring to the node's finite free cokernel presentation.
- `underline Λ` is `(constantSheaf J.toGrothendieck RingCat).obj (RingCat.of Λ)`.
  `underline M` and `underline N` are the objects of `siteConstantModuleFunctor`.
  This is constant module presheaf sheafification, extending the scalar action along
  `toSheafify` of the constant ring presheaf. Its underlying abelian sheaf is
  definitionally the sheafification of the constant abelian presheaf (Mathlib
  `PresheafOfModules.sheafificationCompToSheaf`). Thus this is the node's actual
  constant-ring module encoding, rather than an unrelated category-valued sheaf.
- The set `I(U)` is represented by an existential presheaf `I : Cᵒᵖ ⥤ Type u`
  together with equivalences `e U` to the actual categorical isomorphisms
  `((siteConstantModuleFunctor ...).obj M).over U.unop ≅ ... N ...`.
  A categorical isomorphism in this category is a pair of module-linear maps
  satisfying both inverse laws, exactly a module-sheaf isomorphism. The equivalences
  are a presentation of the stated sets; no hypothesis about a presheaf supplied by
  a caller is imposed. Specifying this presheaf up to natural equivalence avoids
  introducing a second named implementation of local isomorphism presheaves.
- The first conjunct, quantified over `U V f x`, specifies the restriction:
  apply `(SheafOfModules.overMap R f.unop).mapIso` to the local isomorphism and
  conjugate by `SheafOfModules.overFunctorMap` on its source and target. This is
  precisely further localization, with the canonical identifications of restricted
  modules. It specifies all maps of `I`, not only its objectwise sets.
- `∃ hI : Presheaf.IsSheaf J.toGrothendieck I` is the assertion that this presheaf
  is a sheaf of sets. The witness is used to form the actual sheaf `⟨I, hI⟩`.
- `∃ comparison : (constantSheaf ... (Type u)).obj (M ≅ N) ≅ ⟨I,hI⟩` states
  that the comparison is an isomorphism of sheaves of sets. `M ≅ N` in `ModuleCat Λ`
  is exactly the set of invertible Λ-linear maps, including the unique inverse.
- The final equation is quantified over every object `U` and module isomorphism `a`.
  Evaluating `comparison.hom` on the image of `a` under the set-sheafification unit,
  then applying `e U`, gives `(overFunctor R U.unop).mapIso` of
  `(siteConstantModuleFunctor ...).mapIso a`. Thus the isomorphism is specifically
  the canonical map that sends a constant module isomorphism to its constant
  module-sheaf isomorphism restricted to the slice. A sheafification morphism is
  determined by this unit equation. It is not merely an unspecified isomorphism.

Dependency declarations used:

- `Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck`:
  `CategoryTheory.Precoverage`, its four site classes, and `Precoverage.toGrothendieck`;
  the underlying site record also names `CategoryTheory.Sheaf` and `sheafSections`.
  I read the recorded site convention and the relevant full class signatures.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`,
  the sheafification of `Functor.const Cᵒᵖ`; full definition and docstring read.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently `SheafOfModules R`; its entire module was read. All objects above
  are objects of that category, using the underlying Mathlib spelling directly.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.over`, `overFunctor`, `overMap`, and `overFunctorMap`;
  their definitions and docstrings were read. `Mathlib.CategoryTheory.Sites.Over`
  provides `GrothendieckTopology.over` and `Sheaf.over` with the recorded topology.
- New `Sheaf.CategoryTheory.SiteConstantModuleFunctor`:
  `CategoryTheory.siteConstantModulePresheaf` and `siteConstantModuleFunctor`.
- Proof interfaces are imported directly or transitively:
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
  (`sheafification`, `sheafificationCompToSheaf`, `sheafificationAdjunction`);
  `Mathlib.CategoryTheory.Sites.Sheafification` / `LeftExact`
  (`presheafToSheaf` and exactness of set and abelian sheafification);
  `Mathlib.CategoryTheory.Sites.PreservesSheafification`
  (`sheafifyComposeIso` and the unit compatibility);
  `Mathlib.CategoryTheory.Sites.CoverLifting`
  (`Functor.pushforwardContinuousSheafificationCompatibility`, applied to slice restriction).
  Proof dependencies recorded only through `mathlib_match` are used by those exact APIs.

Edge cases checked against the source and intended mathematics:

- `M = 0`, `N = 0`, or just one zero module: isomorphism sets can be singleton or
  empty; neither nonempty isomorphism sets nor nonzero modules are assumed.
- The zero ring is allowed. Its modules are zero, and the canonical inverse-pair
  description and the constant-sheaf comparison remain valid.
- Empty category, an object with an empty covering, and the maximal topology:
  sheafification may identify all sections, including the constant empty set.
  The theorem asserts an isomorphism after sheafification, never full faithfulness
  of the constant functor, so these cases are included.
- Finite free rank zero and presentations with zero generators or zero relations
  are allowed by `Module.FinitePresentation`; the proof plan includes the empty tuple.
- Identity arrows and composites are handled by the functor `I` and the explicit
  restriction equation, without choosing terminals or pullbacks not supplied by the site.
- Universes: all small sets are taken in one arbitrary universe `u`, including the
  small site's objects and arrows, Λ, modules, and Isom sets. Slice-site module
  morphisms remain in `Type u`. The theorem is polymorphic in `u`; it assumes no
  essential-smallness, size bound on covers beyond the small site, or finite dimension.

Searches for the item:

- `msearch.py` LeanFinder: “On a site the isomorphism sheaf of constant finitely
  presented modules is constant”: 8 hits, chiefly `Sheaf.isConstant_of_iso`,
  `SheafOfModules.IsFinitePresentation`, and condensed-module results; none is this theorem.
- `msearch.py` Loogle: `"SheafOfModules", "Iso"`: 12 hits, mainly `isoMk`, forgetful
  reflection, and free-sheaf isomorphisms; no constant finite-presentation comparison.
- `msearch.py` grep: `constant.*[Mm]odule|[Ii]som.*[Pp]resheaf|isoPresheaf`
  in `Algebra/Category/ModuleCat`: 3 unrelated restriction/sheafification hits.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for constant module,
  isom-presheaf and isom-sheaf names: site-specific constant module constructions,
  duals, and scalar-extension material; no arbitrary-site theorem. The upstream
  blueprint-id search found no occurrence. Name searches for the two new definition
  names and the theorem name found no existing declaration.

Server validation: both delivered modules compile separately in dependency order
via `scompile.py`, nice 19, two threads, 60 seconds per file. No errors or warnings
other than the permitted sorry warning. No local compiler or global build was run.

## New nodes

`def-sf-site-constant-module-functor` constructs the functor from Λ-modules to
modules over the constant ring sheaf on an arbitrary small site. It first forms the
constant module presheaf, then composes with Mathlib's `PresheafOfModules.sheafification`
along the ring-sheafification unit. This is the construction in Stacks 03CY and the
constant modules in 093T. Its underlying abelian sheaf and scalar action are those
of the existing module-sheafification API; no replacement category or sheafification
is constructed. The new node cites the existing site, constant sheaf, sheafification,
and module-sheaf category definitions.

Searches: LeanSearch was unavailable (Internal Server Error), recorded verbatim
with status `unavailable` (the preflight requires a verdict field; no match verdict
is inferred from the failed service). LeanFinder returned 8 hits (`SheafOfModules.unit`, `toSheaf`,
`forgetToSheafModuleCat`, condensed locally constant modules, etc.), none the required
functor. Mathlib grep `constantModule|[Cc]onstant.*[Mm]odule` in
`Algebra/Category/ModuleCat` returned zero hits. The exact service output is retained
in the new node. DAG title search and `blueprint_refs.py search 'constant module'`
found no general-site construction. Existing `def-sc-module-presheaf-constant-modules`
is on topological opens, and `lem-weil-pbc-etale-constant-ring-module-equivalence`
constructs an extension functor on a scheme's small etale site. Neither accepts an
arbitrary small site. The general module-sheafification interface is reused, not
redefined. Upstream/project/name searches found no general-site constant module functor.

## Second reading by NP

I independently read the node, both delivered modules, Stacks
`sites-modules.tex` at `lemma-locally-constant` (093T), and the module
sheafification lemma `lemma-sheafification-presheaf-modules` (03CY).
093T(2) assumes finite presentation of both modules; the locally constant
sheaves F,G introduced there concern its other parts and are not extra inputs
of (2). The source allows a general ring; this node explicitly specializes to
a commutative ring, which the Lean follows without changing the node.

Object, hypothesis, and conclusion checklist (all pass):

1. Small site C: `{C : Type u} [SmallCategory C] (J : Precoverage C)` and
   the four classes `HasIsos`, `IsStableUnderComposition`,
   `IsStableUnderBaseChange`, `HasPullbacks`. I read these class signatures
   and `toGrothendieck`: this is the exact convention recorded by
   `def-weil-pbc-sites-and-cohomology`, without an assumption that all
   categorical pullbacks exist. `J.toGrothendieck` supplies the sheaf topology.
2. Commutative coefficient ring: `(Λ : Type u) [CommRing Λ]`. There is no
   field, nontriviality, characteristic, Noetherian, or finite-ring assumption.
3. Modules M,N: `(M N : ModuleCat.{u} Λ)` and separate
   `[Module.FinitePresentation Λ M] [Module.FinitePresentation Λ N]`.
   I read Mathlib's class and `Module.FinitePresentation.exists_fin'`:
   finite generation with finitely generated relation kernel is precisely
   the finite free cokernel presentation required by the node.
4. Constant ring and modules: `(constantSheaf J.toGrothendieck RingCat).obj
   (RingCat.of Λ)` and the two objects of `siteConstantModuleFunctor`.
   I opened the dependency records and `RingedSiteModules.lean`:
   `ringedSiteModules` abbreviates the same `SheafOfModules` category used
   here. I read `constantSheaf`, `PresheafOfModules.sheafification`,
   `sheafificationCompToSheaf`, and `sheafificationAdjunction`. The new
   functor takes the actual constant module presheaf to its abelian
   sheafification with the extended constant-ring action, as 03CY requires.
5. Sections of I at U: `∃ I : Cᵒᵖ ⥤ Type u, ∃ e : ∀ U, I.obj U ≃ ...`.
   The target of `e U` is the categorical isomorphism type between the
   restrictions of these very two modules to `U.unop`. In `SheafOfModules`
   this means linear natural maps with a two-sided inverse. Equivalences
   merely present the prescribed section sets, and do not assume a sheaf
   or a convenient comparison from the caller.
6. Localization and restriction: I read `GrothendieckTopology.over`,
   `Sheaf.over`, and `SheafOfModules.over`, `overFunctor`, `overMap`,
   `overFunctorMap` in their recorded Mathlib modules. The slice topology
   tests covering sieves on the underlying object, exactly as the dependency
   node states. For `f : U ⟶ V` in Cᵒᵖ, `f.unop : V.unop ⟶ U.unop`
   gives further restriction from C/U to C/V. The first conjunct conjugates
   `(overMap R f.unop).mapIso (e U x)` by `overFunctorMap` at M and N,
   with the source comparison inverted. Its direction and endpoints agree
   with `e V (I.map f x)` for every section x.
7. Sheaf of sets: `∃ hI : Presheaf.IsSheaf J.toGrothendieck I` asserts
   exactly the sheaf condition for that same functor I; `⟨I,hI⟩` retains it.
8. Canonical comparison is an isomorphism:
   `∃ comparison : (constantSheaf ... (Type u)).obj (M ≅ N) ≅ ⟨I,hI⟩`.
   `M ≅ N` is the set of invertible Λ-linear maps, with the uniquely
   determined inverse, rather than all maps or only global sheaf maps.
9. Canonicity: the final equation holds for every U and every `a : M ≅ N`.
   Composing the comparison with the set-sheafification unit gives the
   isomorphism obtained by `siteConstantModuleFunctor.mapIso a`, restricted
   by `overFunctor R U.unop`. The unit universal property determines the
   entire sheaf morphism. Thus an arbitrary noncanonical isomorphism cannot
   satisfy the statement merely by being an isomorphism.

Edge cases pass: the zero module on either side, zero coefficient ring,
empty site, empty coverings, and degenerate topology are all permitted.
No inhabitant of `M ≅ N` is assumed. Sheafification, including sheafification
of the empty set, handles the degenerate topology correctly. Finite ranks
zero and empty relation/generator sets occur in `FinitePresentation`.
There is no scheme nonemptiness or connectedness hypothesis. All binders,
including `u`, are bound. The common arbitrary universe is the dependency's
small-site convention; taking a larger common universe accommodates larger
coefficients and modules, and no finite cardinality bound is imposed.

I also reviewed `def-sf-site-constant-module-functor` as a new definition node.
Its self-contained construction is the constant-presheaf specialization of
03CY, with constant modules as used in 093T. Its two definitions contain real
data; only definitional functor laws are discharged, with no mathematical
statement proved and no sorried data or action. The node's definition kind,
chapter, unit, source, cited dependencies, empty proof fields, search records,
creation record, ancestor/via, audit fields, and Lean record match §5. The
parent cites it. It defines no duplicate module category or sheafification.
No dependency module is added by this delivery.

Independent searches, with different wording from the first worker:

- LeanFinder via `msearch.py`: “Locally invertible linear morphisms between
  sheafifications of constant finitely presented modules” returned eight
  results. These include `SheafOfModules.IsFinitePresentation`,
  `PresheafOfModules.homEquivOfIsLocallyBijective`, and
  `PresheafOfModules.sheafifyHomEquiv'`; their types concern presentations
  or maps out of sheafification, not the canonical local-Isom comparison.
- Loogle via `msearch.py`: `"SheafOfModules", "constant"` returned zero hits.
- Independent `rg` searches in Mathlib's ModuleCat files, the full upstream
  `WeilConjectures`, and project `lean/Sheaf`, using `constantModule`,
  `constant.module`, `module.constant`, `isomPresheaf`, `isomSheaf`, and
  `isomorphism.sheaf`, found specialized constant module constructions but
  no general small-site functor or theorem. Exact proposed names and the
  blueprint id have no upstream match. DAG title searches likewise find
  no existing general-site constant-module functor. I opened the nearby
  `etaleConstantModulePresheaf`, `etaleConstantModuleRealization`, and
  `etaleConstantModuleFunctor`: they require a scheme's small etale site,
  and the latter takes a module-valued sheaf, not a Λ-module. The recorded
  `modulePresheafToConstantModules` has topological opens as its domain,
  not an arbitrary small site. Neither replaces this new definition.
  Existing constant sheafification itself is reused through `constantSheaf`.

No mathematical mismatch was found, and no Lean or node changes were needed.
The theorem docstring follows all four proof steps (gluing inverses,
finite-free Hom, finite-presentation kernel, finite-limit inverse pairs),
with source and blueprint attribution. Both node `lean.statement` fields
were checked verbatim against their file signatures. Both sibling modules
compiled separately through `scompile.py` on the server, nice 19, two threads,
60 seconds per file: the functor in 1.5 s and theorem in 1.4 s, with no errors
or disallowed warnings. The required side-only `RingedSiteModules` import
also compiled in the private overlay. This second reading changes only the
report, preserving the correct statements and constructions.
