## Worker report

The module `lean/Sheaf/AlgebraicGeometry/GlobalDerivedHom.lean` defines
`AlgebraicGeometry.schemeGlobalDerivedHom`, the functor
`D(O_X)^op × D(O_X) ⥤ D(O_X(X)-Mod)` obtained by composing the shared derived
internal Hom with the right derived global-sections functor. It also states the
point-space comparison and resolution computation the definition uses.

The node's scheme hypothesis is the explicit `X : Scheme.{u}` binder. The
`D(O_X)` hypothesis is the `HasDerivedCategory` instance on
`SheafOfModules (moduleRings X.toRingedSpace)`, rendering `[def-pc-derived-category]`.
The target is the derived category of modules over the global-sections ring,
represented by `ModuleCat ((moduleRings X.toRingedSpace).obj.obj (op ⊤))`.
Contravariance in the first and covariance in the second variable are rendered
by `derivedInternalHom`, whose domain is a product with the first factor
opposite. The global derived section functor is
`(RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor`,
which is the `Rp_*` construction of `[def-pc-ringed-spaces-derived-direct-image]`
under the one-point identification. Thus the body is exactly
`derivedInternalHom ... ⋙ schemeDerivedGlobalSections X`.

The module imports and uses the dependency declarations
`AlgebraicGeometry.schemeDerivedCategory` (`Sheaf.AlgebraicGeometry.DerivedCategory`),
`CategoryTheory.derivedInternalHom` (`Sheaf.Algebra.Homology.DerivedInternalHom`),
and `AlgebraicGeometry.RingedSpace.derivedModuleDirectImage`
(`Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage`) in the resolution
comparison. The global-sections functor is
`AlgebraicGeometry.RingedSpace.globalSectionsFunctor`
(`Sheaf.Topology.RingedSpaceModuleCohomology`).

Edge cases checked: no nonemptiness or affineness is assumed for X; the empty
scheme and zero modules are admitted by the same derived-category instances;
`PUnit` is used for the one-point space; the affine case is obtained by the
existing `Scheme.ΓSpecIso` identification, while the definition remains in
`D(Γ(X,O_X))` as required by the source. No statement is believed false.

Searches: `msearch.py leansearch` for global derived Hom (service unavailable),
`msearch.py leanfinder` for global derived Hom of sheaves (only generic
`CategoryTheory.Sheaf.H`, `SheafOfModules.Hom`, and `sheafHom`), `msearch.py
loogle` for derived internal Hom (0 hits), and `msearch.py grep` for
`globalDerivedHom|derivedGlobalSections|global.*RHom|derived.*global.*Hom`
(0 Mathlib hits). `rg` over `lean/Sheaf` and
`WeilConjectures/` found no scheme-level global RHom declaration. The Stacks
source at Tag 0B6A, Section 20.44, explicitly places
`RHom_X(K,L)=RΓ(X,RHom(K,L))` in `D(Γ(X,O_X))` and gives the affine and
underlying-abelian interpretations.

## Earlier second reading (a previous round; superseded)

I reread the node, Tag 0B6A, and the complete module. The scheme, derived-category,
internal-Hom, and global-sections hypotheses all appear explicitly; the product
opposite gives the required variance, and the codomain is exactly
`D(Γ(X,O_X))`. The body uses the recorded internal-Hom declaration and the
right-derived global-sections functor. The only adjustment from the first pass
was removing the trailing `:=` from the recorded signature, matching the
preflight parser's signature extraction. No mismatch remains.


## Second reading by N1

Read the sandbox node and module independently, all four statement-dependency nodes,
their recorded declaration signatures and definitions, the global-sections module,
and the upstream unbounded right-derived-functor construction. The local literature
checkout has no stacks-project directory; read the Stacks cohomology.tex source fetched
from the official stacks/stacks-project repository into the item scratchpad, section
`section-global-RHom` (Tag 0B6A). It assumes a ringed space and arbitrary unbounded
objects of D(O_X), with no Noetherian, separated, perfect, affine, or field hypothesis.
The node specializes this faithfully to schemes. Its source metadata still mentions
Tag 0AA8; the split report and source text identify 0B6A, which the Lean docstrings use.
No node statement correction was required.

Object, hypothesis and clause checklist:

1. X is a scheme: `X : Scheme.{u}`, using Mathlib's `AlgebraicGeometry.Scheme`
   from def-pc-scheme. Verdict: exact; no additional geometric property.
2. D(O_X) is the unbounded derived category of all O_X-module sheaves:
   `schemeDerivedCategory X`, unfolding to `DerivedCategory (SheafOfModules.{u}
   (moduleRings X.toRingedSpace))`, with the recorded `HasDerivedCategory.{w}`
   binder from def-pc-derived-category. Verdict: exact; not D_QCoh or D-plus.
3. A is Γ(X,O_X): `(moduleRings X.toRingedSpace).obj.obj (op ⊤)` is the underlying
   global-sections ring, retaining its module action. The target category is
   `DerivedCategory (ModuleCat.{u} A)`, with an independently chosen localization
   universe `wA`. Verdict: exact; not merely abelian-group cohomology.
4. The point and p with identity p-sharp: `globalSectionsPoint X` pushes forward
   X.presheaf along the constant map to `PUnit.{u+1}`; `toGlobalSectionsPoint X`
   has `c := 𝟙 _`. The inverse-image whole open is the whole X, so the point ring
   is A; on the empty open the sheaf condition forces the zero ring.
   Verdict: correct, including for the empty scheme.
5. Modules on the point are A-modules: the old file only described this in prose
   and asserted finite-colimit preservation. Added
   `globalSectionsPoint_module_equivalence`, whose equivalence functor is
   isomorphic to evaluation. Verdict: now explicitly rendered.
6. RΓ is Rp_* under this identification: `schemeDerivedGlobalSections X` is the
   existing unbounded `Functor.rightDerivedFunctor` of the shared
   `RingedSpace.globalSectionsFunctor`. The old file lacked the actual comparison
   with the dependency's `derivedModuleDirectImage`. Added
   `schemeDerivedGlobalSections_point_comparison`, a natural isomorphism between
   Rp_* followed by exact point evaluation and RΓ. `globalSectionsPointEvaluation`
   is an abbreviation of the existing evaluation with A written in the shared
   ring carrier; its named additivity/exactness instances support elaboration.
   Verdict: exact; the auxiliary point localization is needed only for this
   comparison, not as an extra hypothesis on the main definition.
7. Every K-injective resolution computes RΓ: existing
   `schemeDerivedGlobalSections_computed_by_resolution`, for arbitrary complexes
   K,I and `s : K ⟶ I`, with `[QuasiIso s] [I.IsKInjective]`, identifies RΓ(QK)
   with Q of termwise Γ(I). Verdict: exact; no boundedness or termwise-injectivity
   assumption. The comparison is an isomorphism, as “represented by” requires.
8. For arbitrary P,Q, RHom_X(P,Q) is RΓ(X,RHom(P,Q)):
   `schemeGlobalDerivedHom` is exactly `derivedInternalHom
   (Opens.grothendieckTopology X) X.sheaf ⋙ schemeDerivedGlobalSections X`.
   Opened def-pur-derived-internal-hom's declaration: it is the localized Hom
   complex with a functorial K-injective replacement, on the same module carrier.
   Verdict: exact, no special-case internal Hom or private replacement.
9. Contravariance in P and covariance in Q: the domain is
   `(schemeDerivedCategory X)ᵒᵖ × schemeDerivedCategory X`; both factors are
   unrestricted and the composite is a functor. Verdict: exact quantifier order.
10. For X = Spec R it is in D(R): the old file imported ΓSpecIso but supplied
    no scalar-transport construction. Added `affineGlobalDerivedHom (R : Type u)
    [CommRing R]`, composing the same RHom with exact restriction of scalars
    along `(Scheme.ΓSpecIso (.of R)).inv.hom`. Verdict: exact; R is an arbitrary
    commutative ring, and this is transport through a ring isomorphism.
11. Forgetting A gives an object of D(Ab): `schemeGlobalDerivedHomAb` composes
    the same functor with `(forget₂ (ModuleCat A) AddCommGrpCat).mapDerivedCategory`.
    Verdict: exact and retains the shared RHom rather than redefining it.

Edge cases: the empty scheme is allowed; Γ of its structure sheaf is the zero
ring and the construction still applies. Zero complexes and zero modules are
allowed. There is no index set, natural-number bound, nonemptiness, characteristic,
field, or finiteness restriction. Complex degrees range over all integers.
`u`, `w`, `wA`, `wAb`, `wPt`, `wR` are all explicitly bound; the point has exactly
the scheme's space universe. The independent derived-category universes are chosen
localization structures (standard choices exist), not restrictions on X or modules.

Independent searches, using phrases different from the worker's:
- LeanFinder: “derived global sections functor ringed space modules”: eight hits,
  including sectionsFunctor, tilde, Γ and scheme Modules, none this RHom notion.
- Loogle: `"rightDerivedFunctor"`: generic Kan-extension and right-derived-functor
  infrastructure, no scheme O_X-module global Hom definition.
- LeanSearch: “right derived functor of evaluation of module sheaves at the whole
  ringed space”: unavailable (Internal Server Error); no negative verdict inferred.
- msearch grep: `derivedModuleDirectImage.*point|affineGlobalDerivedHom|
  globalSectionsPoint|schemeDerivedGlobalSections_point_comparison`: no Mathlib hit.
- Direct rg in Mathlib, WeilConjectures and lean/Sheaf with global-derived-Hom,
  derived-global-sections and global-RHom variants: upstream Etale and ProEtale
  global sections use different sites/coefficient sheaves. Opened Etale's
  GlobalSections module to verify this. Landed `rhom_global_sections` computes
  H^0 of internal Hom, not the global derived Hom complex; opened its signature.
  The affine-QCoh equivalence uses derived Γ restricted to D_QCoh and states an
  equivalence, not this unrestricted bifunctor. No usable duplicate was found.
  Exact new names were also searched in upstream, project Lean and the name map.

Repairs: added the module equivalence, the point derived comparison and the affine
scalar transport; added named exactness support for point evaluation. Removed the
unused GammaSpecAdjunction import (ΓSpecIso itself is in Scheme). Added a main
-declarations overview and recorded every delivered declaration. The main RHom
signature and definition remain unchanged, with lean.statement copied verbatim.
No new DAG notion or dependency module is needed: these are precisely clauses
already carried by the item's own definition node. All new theorem proofs are
`sorry`, each with a source, blueprint id and a complete natural-language argument;
all definition data is concrete. No private definitions, file-local notation or
local instances. No disputed statement remains. Local single-file compilation
passed; deliver2 supplies the final server compilation and preflight.
