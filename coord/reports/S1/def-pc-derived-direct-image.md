## Worker report

The module lean/Sheaf/AlgebraicGeometry/SchemeDerivedDirectImage.lean defines the
scheme specialization of the existing ringed-space derived direct image, its integer-degree
cohomology-sheaf functor, and its application to modules in degree zero. No proof, new node,
or dependency module is needed; the item's statement and dependencies are unchanged.

Clause-by-clause correspondence:

- A morphism f : X → S of schemes: `{X S : Scheme.{u}}` and `(f : X ⟶ S)`.
  Mathlib's Scheme and Scheme.Hom are precisely the recorded scheme dependency.
- The underlying ringed-space morphism: `f.toLRSHom.toShHom`; the toRingedSpace
  abbreviations of X and S are their underlying ringed spaces.
- Rf_* : D(O_X) → D(O_S): `schemeDerivedDirectImage f` has type
  `schemeDerivedCategory X ⥤ schemeDerivedCategory S`. Its body is exactly
  `RingedSpace.derivedModuleDirectImage f.toLRSHom.toShHom`, so this is a specialization
  of the dependency, not a second K-injective construction.
- Computation by K-injective resolutions is inherited from that dependency's
  `derivedModuleDirectImage_computed_by_resolution`, with the same module-sheaf carrier.
- For any E in D(O_X) and integer i, R^i f_* E = H^i(Rf_*E):
  `(schemeHigherDirectImage f i).obj E` is definitionally
  `(DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) i).obj
      ((schemeDerivedDirectImage f).obj E)`.
  The output is an O_S-module sheaf, with no quasi-coherence restriction.
- For an O_X-module F, application as a complex in degree 0:
  `(schemeModuleHigherDirectImage f i).obj F` first applies
  `DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0`,
  then applies the preceding functor. This uses the standard degree-zero embedding.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom
  (scheme structure is locally ringed space plus local affine neighborhoods; morphisms
  are the underlying locally ringed-space morphisms).
- Sheaf.AlgebraicGeometry.DerivedCategory: AlgebraicGeometry.schemeDerivedCategory;
  its signature uses the shared SheafOfModules (moduleRings X.toRingedSpace) carrier
  and a HasDerivedCategory instance. This module is imported directly.
- Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage:
  AlgebraicGeometry.RingedSpace.derivedModuleDirectImage and its K-injective computation.
  The full declaration and docstrings were read; it is the existing unbounded
  rightDerivedFunctor of moduleDirectImage. This module is imported directly.
- Mathlib derived-category homologyFunctor and singleFunctor are used via these imports;
  their full signatures and defining constructions were read in HomologySequence.lean
  and Basic.lean.

Universes u, wX and wS are explicit. HasDerivedCategory binders select the existing
localizations, as required by the dependency signatures; they are not extra geometric
hypotheses. The module uses no file-local notation, instance, or private definition.

Edge cases checked before writing: any integer i, including negative and zero degrees;
any derived object, including unbounded complexes and zero objects; any module sheaf,
including zero; identity morphisms and morphisms from an empty scheme. There are no
properness, boundedness, quasi-coherence, finiteness, or nonemptiness conditions. The two
localization universes may differ. No clause asserts preservation or vanishing beyond
the definition itself.

Searches (the msearch output is also recorded in searches.jsonl):

- leanfinder, "derived direct image of sheaves of modules on schemes and higher direct
  image cohomology sheaves": eight results, underived Scheme.Modules.pushforward and
  SheafOfModules.pushforward and their adjointness/section declarations; no exact match.
- loogle, "CategoryTheory.Functor.rightDerivedFunctor, DerivedCategory.homologyFunctor":
  zero hits; unknown identifier CategoryTheory.Functor.rightDerivedFunctor in the service.
- msearch grep, "higherDirectImage|derivedDirectImage|derivedModuleDirectImage": zero
  Mathlib hits.
- leansearch, "unbounded derived pushforward sheaves of modules on schemes cohomology
  higher direct image": unavailable, Internal Server Error.
- rg over WeilConjectures and lean/Sheaf for the above names and singleFunctor: the
  recorded ringed-space definition exists and is reused. Scheme.Modules.higherDirectImage
  in WeilConjectures/AlgebraicGeometry/Cohomology/DirectImage.lean:170 was read in full:
  it is `(pushforward f).rightDerived q`, for q : ℕ and modules, with X.Modules' own
  category instance; it does not define the unbounded scheme derived direct image or
  integer-degree higher images of arbitrary derived objects. Our module-case clause
  simply specializes the same H^i(Rf_*E) definition to degree zero, without a second
  resolution construction. The other hit in WeilSheaf/OpenImmersion.lean is an etale
  open-immersion specialization, a different site and carrier.
- rg for def-pc-derived-direct-image in WeilConjectures: no hits.
- rg for schemeDerivedDirectImage, schemeHigherDirectImage, schemeModuleHigherDirectImage
  in Mathlib, WeilConjectures, dag/lean_names_upstream.json and lean/Sheaf: no hits.

Source checking: the local blueprint file named in the node is absent on this machine;
opened https://stacks.math.columbia.edu/tag/0A1G, which uses Rf_* on D(O_X) and uses
modules placed in degree zero. The node explicitly delegates its construction to the
ringed-space definition; its landed module supplies it. No statement correction or
STATEMENT-DISPUTED issue was found.

Server validation: scompile.py S1 def-pc-derived-direct-image compiled the complete
64-line module in 3.8 seconds, exit code 0, with no warnings.

## Second reading by S1

Independent second reader: read the sandbox node and all 64 lines of its module,
the three dependency nodes and their recorded declarations, and the Mathlib
homologyFunctor and singleFunctor definitions. Verdict: every clause matches;
no Lean or node correction is needed. No new nodes or dependency modules occur.

Source: the local literature checkout contains no Stacks .tex sources. Read the
upstream Stacks tags/tags mapping and the actual sources at
https://raw.githubusercontent.com/stacks/stacks-project/master/perfect.tex
(label section-cohomology-and-base-change-final, Tag 0A1G) and
https://raw.githubusercontent.com/stacks/stacks-project/master/cohomology.tex
(label section-unbounded, Tag 079V). The first uses the functor in base-change
results; the second constructs it for arbitrary ringed-space morphisms on
unbounded derived categories using functorial K-injective resolutions. The
finite-presentation, perfectness, flatness and proper-support assumptions in
0A1G belong to its base-change lemmas, not to this definition. No missing
ambient geometric hypothesis was found.

Object/hypothesis/clause checklist (each verdict: exact):

1. Schemes X and S, and a morphism f : X → S: `{X S : Scheme.{u}}`,
   `(f : X ⟶ S)`. Read Scheme.local_affine and Scheme.Hom in the recorded
   Mathlib.AlgebraicGeometry.Scheme module. Hom is precisely a morphism of
   the underlying locally ringed spaces; no extra property of f is assumed.
2. Underlying ringed spaces with their structure sheaves and morphism:
   `X.toRingedSpace`, `S.toRingedSpace`, `f.toLRSHom.toShHom`.
   `moduleRings` gives the shared ring-sheaf carrier, not a coefficient field
   or the etale site.
3. D(O_X) and D(O_S): `schemeDerivedCategory X` and
   `schemeDerivedCategory S`, from Sheaf.AlgebraicGeometry.DerivedCategory.
   Read its full signature and body: the unbounded derived category of
   `SheafOfModules.{u} (moduleRings X.toRingedSpace)`, respectively S.
   Its HasDerivedCategory binders choose the shared localizations. They do
   not impose boundedness or quasi-coherence.
4. Rf_* is the dependency's ringed-space direct image, computed by
   K-injectives: `schemeDerivedDirectImage f` is an abbreviation whose entire
   body is `RingedSpace.derivedModuleDirectImage f.toLRSHom.toShHom`.
   Read the dependency's moduleDirectImage, derivedModuleDirectImage and
   derivedModuleDirectImage_computed_by_resolution: direct image uses inverse
   image opens and the structural scalar map, and its derived functor is
   computed by any quasi-isomorphism into a K-injective complex. This
   specialization shares that construction and its comparison theorem.
5. Every E in D(O_X), every integer i, and R^i f_* E = H^i(Rf_* E):
   `schemeHigherDirectImage (f : X ⟶ S) (i : ℤ)` is the functor composite
   `schemeDerivedDirectImage f ⋙ DerivedCategory.homologyFunctor
   (SheafOfModules.{u} (moduleRings S.toRingedSpace)) i`. Applied to E,
   its body is exactly the stated cohomology sheaf. Mathlib's homologyFunctor
   uses ComplexShape.up ℤ, so this is cohomological degree i, without a sign
   reversal. The output is an O_S-module sheaf, with no restriction to QCoh.
6. For every O_X-module F, view F in degree zero first:
   `schemeModuleHigherDirectImage f i` is
   `DerivedCategory.singleFunctor (SheafOfModules.{u}
   (moduleRings X.toRingedSpace)) 0 ⋙ schemeHigherDirectImage f i`.
   Read singleFunctor's construction through the homotopy-category single
   functor and Qh: it is the ordinary degree-zero embedding. The order of
   application and the quantification over all modules agree with the node.

Edge cases: i ranges over all integers, including 0 and negative degrees;
E may be unbounded or zero and F may be zero. Empty schemes and all morphisms
between them permitted by Scheme.Hom remain included. There is no index set,
nonemptiness, characteristic, field, Noetherian, properness or finiteness
binder. The explicit universe u ranges over all scheme sizes (unequal sizes
can be placed in a common universe); wX and wS are independent localization
universes. No variable or universe is unbound.

Independent searches, using different wording from the worker:

- msearch leanfinder: "unbounded derived pushforward functor ringed space
  scheme cohomology sheaf" returned eight underived pushforward/adjunction
  declarations, no exact scheme total derived-image definition.
- msearch loogle: "DerivedCategory.homologyFunctor" returned the shared
  Mathlib homology functor and its comparisons, which the module reuses.
- msearch leansearch: "total derived pushforward on unbounded derived
  categories of structure sheaf modules" was unavailable (Internal Server
  Error); no absence inference was drawn from this service failure.
- msearch grep: "derived.*pushforward|derived.*directImage|higherDirectImage"
  returned no Mathlib hits. Independently searched Mathlib's algebraic
  geometry sources, all WeilConjectures algebraic geometry modules and
  lean/Sheaf for derived pushforward/direct image and higher direct image;
  also searched the proposed names in lean/Sheaf, WeilConjectures and
  dag/lean_names_upstream.json: no exact existing declaration.
- Opened Scheme.Modules.higherDirectImage in upstream Cohomology/DirectImage.lean:
  it is `(pushforward f).rightDerived q` for q : ℕ on X.Modules with its
  distinct category instance. It does not provide the arbitrary derived
  object or integer-degree definition here. The module-case composite reuses
  the new general functor rather than constructing another resolution.
- Opened Sheaf.AlgebraicGeometry.DerivedDirectImageComposition: its declarations
  concern bounded-below abelian etale sheaves, not O_X-modules on opens.
  The ringed-space declaration is the exact dependency and is reused.

H5/H6/H8/H9: all three definitions have explicit data and no sorry; no theorem
is proved. Each docstring names its source and blueprint id. The node has no
proof steps to transcribe. Imports are used, names are global, and there is
no private definition, local notation or instance. The recorded lean.statement
is verbatim the primary abbreviation's signature. No mismatch was found;
only this independent review section was appended, preserving Worker report.

Validation: scompile.py S1 def-pc-derived-direct-image on the unchanged complete
module compiled in 3.3 seconds, exit code 0, with no warnings.
