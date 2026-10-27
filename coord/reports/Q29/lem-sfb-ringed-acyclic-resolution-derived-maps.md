## Worker report

The delivery states `CategoryTheory.ringedAcyclicResolutionDerivedMaps` in
`Sheaf.CategoryTheory.RingedAcyclicResolutionDerivedMaps`. Its single proof is `sorry`.
There are no new definitions, no new DAG nodes, no dependency repairs, and no
natural-language statement correction. The accepted Q58 stage-1 split is preserved.
The old BLOCKED ending concerned stage 1; the live stage-2 queue names this item and
it had no Lean record. This is the stage handoff explicitly allowed in brief-stage2 §0.

The theorem packages the standard derived functors with their universal units, then
states the acyclic comparison theorem for all the modules and resolutions in the node.
The derived functors are specified by Mathlib's `IsRightDerivedFunctor`, together with
invertibility of the units on K-injective complexes. This is the universal-pair
interface of `def-sfb-right-derived-functor`, rather than a second derived construction
or arbitrary replacement maps. There is no choice of data from a mere existence proof
in a definition: this delivery contains just a theorem statement.

Hypothesis and clause audit:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Two small sites, each with a terminal object | `C D : Type u`, `[SmallCategory C]`, `[SmallCategory D]`, `[HasTerminal C]`, `[HasTerminal D]`, and `J K : GrothendieckTopology ...`. The existing site API uses its associated Grothendieck topology for sheaves. |
| Common coefficient universe and localization size convention | Both rings, module carriers and `AddCommGrpCat` use `u`. The three explicit `HasDerivedCategory.{w}` instances choose the common localization universe. No site universe is forced to a different universe. |
| Commutative ring sheaves A,B | `A : Sheaf J CommRingCat.{u}` and `B : Sheaf K CommRingCat.{u}`; `sheafCompose ... (forget₂ CommRingCat RingCat)` supplies their underlying ring sheaves to the recorded module and ringed-topos definitions. |
| Morphism of ringed topoi f, with induced module direct image | The binder is the recorded `RingedToposMorphism`; every occurrence of direct image is its `f.modules`. The ring map, geometric adjunction and induced module action are exactly that structure, not an arbitrary additive functor. |
| Enough injectives in both module categories | The two explicit `EnoughInjectives (coefficientModules ...)` binders. The abelian instances are the small-site Mathlib module-sheaf instances. |
| Global sections | The existing `coefficientSections R = SheafOfModules.toSheaf _ ⋙ Sheaf.Γ ...` abbreviation. The item gains the already landed definition node `def-sfb-coefficient-module-global-sections` in `stmt_deps`; no duplicate is defined. |
| The canonical identity Gamma_D f_* = Gamma_C | The isomorphism `t` is pinned, not arbitrary: `zC,zD` are global elements specified sectionwise by `Sheaf.ΓRes`; the third conjunct says their images under `f.adj.homEquiv` agree through `f.underlying`. This is the geometric-adjunction identification, including the coefficient action encoded in f. |
| Derived sections and direct image, with their canonical units | `RG`, `RH`, `Rf` and `ηG`, `ηH`, `ηf` satisfy their total right-derived universal properties and the K-injective unit computation. Different universal pairs are uniquely identified compatibly with these units, exactly as in the recorded derived-functor dependency. |
| Canonical derived composition comparison | `κ : Rf ⋙ RG ≅ RH`, uniquely normalized by `ηG(f_*I) ≫ RG(ηf(I)) ≫ κ(QI) = Q(t_I) ≫ ηH(I)` for every complex I. This is the inverse direction of the normalized 0D6E comparison used in the node's definition of res_f. It prevents any arbitrary automorphism of derived sections. |
| Modules M,N and coefficient map phi | `M : coefficientModules B`, `N : coefficientModules A`, `φ : M ⟶ f.modules.obj N`. |
| Augmented resolutions r,s | `P,S` are integer-indexed cochain complexes, with maps `r : M[0] ⟶ P` and `s : N[0] ⟶ S`, each a `QuasiIso`. Here `[0]` is the existing `CochainComplex.singleFunctor ... 0`. No injectivity or monomorphism is added. |
| Zero in negative degrees | `[P.IsStrictlyGE 0]` and `[S.IsStrictlyGE 0]`. |
| All terms section-acyclic | `∀ q : ℤ, (coefficientSections B).rightAcyclic (P.X q)` and the analogous A statement. The recorded upstream `rightAcyclic X` means all `(q+1)`-st right derived functors vanish, exactly all positive degrees. |
| A chain map u over the augmentations | `u : P ⟶ (f.modules.mapHomologicalComplex (.up ℤ)).obj S` and the equation `r ≫ u = single.map φ ≫ singleMapHomologicalComplex.inv.app N ≫ f_*(s)`. The middle is the canonical single-complex identification, necessary because applying f_* to a zero complex need only preserve it up to isomorphism. |
| The category D+(Ab) | `hM,hN,hP,hS` assert membership of the four specified derived objects in `DerivedCategory.TStructure.t.plus`; both components of `c` are explicitly isomorphisms in `DerivedCategory.Plus AddCommGrpCat.{u}`. These are conclusions, not extra hypotheses. |
| Canonical isomorphisms c_r,c_s in the stated directions | `c.1` goes from `Q Gamma_B(P)` to `RG(Q M[0])`; `c.2` goes from `Q Gamma_A(S)` to `RH(Q N[0])`. The pair exists uniquely. |
| The comparisons use extensions into injective resolutions | For every nonnegative integer-indexed termwise-injective I, every quasi-isomorphism `i : M[0] ⟶ I`, and every `a : P ⟶ I` with `r ≫ a = i`, the first normalization is `c.1.hom.hom ≫ RG(Qi) = Q Gamma_B(a) ≫ ηG(I)`. The second normalization is the identical N,S version for `j,b`. Since the units on I and the localized augmentations are invertible, these say exactly `c_r = rho_I^-1 Q Gamma(a)` and its s counterpart, with `rho_I = RG(Qi) ≫ ηG(I)^-1`. |
| Independence of extensions and injective resolutions | Both normalization clauses quantify over EVERY such I,i,a or I,j,b. Uniqueness of the comparison pair, together with these equations, gives the same c_r,c_s for all choices, with no selected lift. |
| Equality c_s Q Gamma(u) = res_f(phi) c_r | The final equality is `Q Gamma_B(u) ≫ Q(t_S) ≫ c.2.hom.hom = c.1.hom.hom ≫ RG(Q(phi[0]) ≫ ηf(N[0])) ≫ κ(QN[0])`, with the explicit single-complex identification included in `phi[0]`. This is precisely the source arrow through Rf followed by the canonical composition comparison. |
| Equality before cohomology | The final maps are derived-category morphisms. The `.hom.hom` projections are the faithful inclusion of D+(Ab) into D(Ab), so the displayed equality is equivalently the equality in the full D+(Ab). No cohomology functor is applied. |
| Coefficient-compatible pullback maps | Phi is any module map into the actual induced f_*. Substituting the specified coefficient pullback map gives this case directly; there is no restriction on phi or its lift u. |
| Identity morphism: all maps of resolutions | f is arbitrary and includes the identity ringed-topos morphism. Thus the same universally quantified formula applies to every augmentation-preserving u for f=id. |
| No flatness, exact f^*, or termwise injectivity of P,S | None occurs. Only auxiliary comparison targets I in the universal normalization clauses are required to be termwise injective. |

Dependency declarations used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`
  is the existing site convention; sheaves are formed on its associated Grothendieck
  topology. `Mathlib.CategoryTheory.Sites.GlobalSections`: `Sheaf.Γ`, `Sheaf.ΓRes`
  and the geometric global-element description are used through the landed API.
- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`,
  especially `modules`, `adj`, and `underlying`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules`, `toSheaf`.
- `Sheaf.CategoryTheory.DerivedSectionsScalarCoherence`:
  `CategoryTheory.CoefficientDerivedSections.coefficientModules`, `coefficientSections`.
  The owning definition node, added to `stmt_deps`, is already landed and existing:true.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `EnoughInjectives`, `Injective`.
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`: `InjectiveResolution`;
  its integer-indexed formulation here is a nonnegative injective complex with a
  quasi-isomorphism from the degree-zero complex, exactly the recorded notion.
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`:
  `CategoryTheory.Functor.rightAcyclic` (the actual definition, not a copy).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`: `DerivedCategory.Plus`,
  `DerivedCategory.TStructure.t`. The size-convention node is metatheoretic, so the
  explicit universes implement it; it has no declaration to import.
- `Mathlib.CategoryTheory.Functor.Derived.RightDerived`: `Functor.IsRightDerivedFunctor`.
  The imported `RightDerivedFunctorOfQuasiIsoResolutions` module records the same
  universal-pair specification and its canonical K-injective computation.

All stated proof-dependency modules are imported as the stage-3 plan. The only
proof dependency with no recorded Lean declaration is
`lem-sfb-ringed-topos-injective-pushforward-global-acyclic`; its future import remains
for the maintainer once that independent proof prerequisite is stated. It is not needed
to type this stage-2 statement. No missing mathematical notion required a new node.
The proof docstring follows all eight accepted steps, including the normalized
composition comparison and the common injective target, without asserting that f_*I
is injective or that module inverse image is exact.

Edge cases checked before drafting:

1. Zero modules and zero resolutions: the augmentations can be quasi-isomorphisms,
   all acyclicity conditions hold, and the comparison and final equality have their
   expected zero-object interpretations.
2. Point site with ring Z and the exact global-sections functor: P=Z[0] is an allowed
   acyclic resolution even though its degree-zero module is not injective. Thus the
   statement does not silently restrict P,S to injective resolutions.
3. Degree zero is included in the complexes, while acyclicity tests precisely positive
   derived degrees; the negative complex terms are zero by IsStrictlyGE, not by a
   cohomological boundedness weakening.
4. Identity f with distinct resolutions and every augmented u is included without any
   chosen comparison lift. Taking u to be an identity or a zero coefficient map is
   included as well.
5. Nonflat change of rings, for example Z to F_p on the point topos, is allowed:
   RingedToposMorphism requires left exactness only of the underlying set inverse
   image, never exactness of tensor module pullback.
6. An empty presented category has no terminal object, so is excluded by the node's
   stated hypothesis itself. Trivial/zero sheaf cases on sites with a terminal object
   remain admitted. The universe binders exclude no small site in the common universe.

Searches actually run (full outputs are retained in the sandbox search log):

- `msearch.py leanfinder`, query "Acyclic resolutions compute canonical derived global
  section maps for a morphism of ringed topoi": eight hits, led by
  `Functor.rightDerived_map_eq`, `InjectiveResolution.toRightDerivedZero'_naturality`,
  and `InjectiveResolution.rightDerived_app_eq`. These are higher-derived/cohomology
  statements and do not state the normalized equality in D+(Ab).
- `msearch.py loogle`, query `"rightDerived", "NatTrans"`: twelve hits including
  `Functor.rightDerivedNatTrans` and its factorization lemmas. They give general
  transformations of derived functors, not this two-site acyclic comparison theorem.
- `msearch.py grep`, regex `acyclic.*[Rr]esolution|[Rr]esolution.*[Aa]cyclic`,
  subdirectory `CategoryTheory`: zero hits.
- `msearch.py grep`, regex `rightDerived|[Aa]cyclic`, subpath
  `CategoryTheory/Abelian/RightDerived.lean`: five reported hits concerning ordinary
  right derived functors and injective resolutions; no full statement match.
- `rg` of the item id in both `lean/WeilConjectures` and `lean/Sheaf`: no hits before
  drafting. Searches for acyclic resolutions, derived sections and global sections in
  these trees located the existing Acyclic, KInjectiveDerivedMapComputation,
  DerivedSectionsScalarCoherence, and RingedSiteCohomologyFmapCalculus interfaces.
  The last module's `map_acyclic` was read: it asserts equality after applying
  homology in a natural-number-indexed model, rather than equality in D(Ab).
  The upstream `quasiIso_map_of_rightAcyclic` gives the quasi-isomorphism criterion,
  not the ringed-topos change-of-site map or its derived normalization.
- `rg` of the DAG for coefficientModules/coefficientSections found the already landed
  `def-sfb-coefficient-module-global-sections`, which is reused directly. No new
  notion or definition node is introduced.

Sources read: the live node and every statement dependency's statement/record, the
recorded declarations and docstrings, Stacks sites-cohomology.tex
`lemma-derived-pushforward-composition` (0D6E), derived.tex `lemma-leray-acyclicity`
(015E), and the current `literature/blueprint/latest` direct-image stability proof.
There is no STATEMENT-DISPUTED issue and no change to the unit's statement or route.

Validation uses only the prescribed server `scompile.py`, with the unchanged 60-second
limit per file. The theorem scopes an increased elaborator heartbeat budget because its
universal derived-pair specification and four D+ vertices exceed Lean's default total
heartbeat count. This does not change the compiler wall-clock limit. No local build,
shared source edit or direct Git command was run.

The final standalone server compile is clean: sandbox 25.4 seconds and library module
32.1 seconds, with no non-sorry warnings. The node record's signature was compared
verbatim with the source. Only `lean` and the addition of the existing global-sections
definition to `stmt_deps` differ from the live item; there is one named theorem with
one `sorry`, and every Lean line is at most 100 characters.

## Second reading by Q29

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
