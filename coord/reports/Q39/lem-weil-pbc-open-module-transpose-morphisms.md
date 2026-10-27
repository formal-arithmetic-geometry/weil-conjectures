## Worker report

The module `Sheaf.Topology.OpenModuleTransposeMorphisms` states
`TopologicalSpace.Opens.exists_openModuleTransposeMorphisms`, with its proof `sorry`.
It supplies two transparent helper abbreviations for the already constructed Mathlib
functors. No definitions contain postponed data or proof fields. The node is unchanged
outside `lean`; no dependency repair, new node, or statement correction is needed.

Source read: `literature/stacks-project/sheaves.tex`, lemma-adjoint-push-pull-presheaves-modules
(Tag 008U), including its two displayed transpose rules and proof, and lemma-j-pullback
(Tag 00A0), clauses (1), (2), (4), (5), its extension to modules and proof.

Clause-by-clause correspondence:

- A topological space with a sheaf of commutative rings is bundled as
  `(X : RingedSpace.{u})`, following the project's convention. Its ring sheaf is
  the recorded `AlgebraicGeometry.moduleRings X`; `(U : Opens X)` is the arbitrary open.
  The module universe `w` is independent and explicit.
- Opens contained in U are objects `W : Over U`. Mathlib's `U.overEquivalence`
  identifies this site with opens of the topological subspace. The restricted ring
  sheaf is `(moduleRings X).over U`, with values on `W.left` and inherited restrictions.
- The module presheaves `P`, `P'` are `PresheafOfModules.{w} (moduleRings X).obj`;
  `Q`, `Q'` are `PresheafOfModules.{w} ((moduleRings X).over U).obj`.
  Mathlib's `PresheafOfModules.obj` is a section module and `map` is a linear map
  into restriction of scalars, hence a semilinear restriction in the stated sense.
  Its `Hom.app` consists of linear maps, with the `Hom.naturality` restriction law.
- R is `openPresheafModuleRestriction X U`, exactly
  `PresheafOfModules.pushforward₀ (Over.forget U) (moduleRings X).obj`.
  Its objects evaluate P on `W.left`, its restrictions are inherited, and its map
  on a morphism evaluates that morphism on `W.left`. The stipulated structures
  are actual Mathlib structures, so no extra assumption on their existence is needed.
- D is `openPresheafModuleDirectImage X U`, exactly
  `PresheafOfModules.pushforward (SheafOfModules.pushforwardOver U).hom`.
  The underlying functor is `Over.star U`: at V it evaluates on the open U product V,
  canonically U intersection V. The ring morphism is restriction along `prod.snd.op`,
  so the scalar action is precisely through the prescribed rho_V. On morphisms it
  evaluates nu on that same intersection. These are existing functor constructors.
- The theorem quantifies existentially over families of morphisms Phi and Psi for all
  P,Q. These are functions into actual module-presheaf Hom types; linearity (including
  addition and zero) and restriction compatibility are built into their types.
- Its first conjunct is the exact forward formula:
  `(Φ P Q α).app (op V) s = α.app (op ((Over.star U).obj V))
  (P.map (prod.snd : U ⨯ V ⟶ V).op s)`.
- Its second conjunct is the exact reverse formula using the canonical identification:
  `(Ψ P Q β).app (op W) s = Q.map ((Over.forgetAdjStar U).unit.app W).op
  (β.app (op W.left) s)`. The unit identifies W with U intersection W, and thus
  also identifies the scalar restriction with the identity. This is the required
  identification of the section model, rather than an arbitrary comparison map.
- The third conjunct quantifies over precisely mu:P'->P, nu:Q->Q', and alpha:R P->Q.
  Lean composition is written in diagrammatic order; its equality reads
  `Φ P' Q' (R.map μ ≫ α ≫ ν) = μ ≫ Φ P Q α ≫ D.map ν`.
- The fourth conjunct gives the displayed common component for every V and s:
  nu at the intersection, applied to alpha there, applied to mu there, applied to
  the restriction of s. The third conjunct also gives this value for the other
  composite. Notice that mu is evaluated at the underlying open
  `((Over.star U).obj V).left`, whereas alpha and nu use its object of `Over U`.
- The fifth and sixth conjuncts assert `Presheaf.IsSheaf` for R applied to each
  module sheaf on X and D applied to each module sheaf on U. Their binders use the
  dependency's `CategoryTheory.ringedSiteModules` directly. Together with
  `SheafOfModules.Hom.val` (the same underlying module-presheaf morphism), these
  express application of every preceding formula and equality to module sheaves.
  Restriction and direct image do not require a sheafification choice here.

Dependency declarations read and used:

- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`,
  `PresheafOfModules.sheafification` and its adjunction: this is the first dependency's
  recorded declaration. The presheaf and morphism notions from that module's public
  imports are `PresheafOfModules`, `PresheafOfModules.Hom`, and `PresheafOfModules.map`.
  This statement concerns the presheaf part, so does not apply sheafification itself.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  the second dependency's recorded arbitrary-site category, transparently
  `SheafOfModules`, whose Hom type is precisely an underlying presheaf morphism.
- `WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris`,
  `AlgebraicGeometry.moduleRings`: the shared ringed-space structure sheaf convention.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward`,
  `PresheafOfModules.pushforward₀`, `PresheafOfModules.pushforward`, with their full
  definitions read; `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
  `SheafOfModules.pushforwardOver`, whose components are exactly ring restrictions.
  `Mathlib.Topology.Sheaves.Module` supplies the topological specialization and
  the existing identification `TopologicalSpace.Opens.sheafOfModulesEquivOver`.

Edge cases checked before writing: X empty; U empty or top; V disjoint from U;
W empty; zero modules and zero morphisms; identity mu or nu. No nonempty, nonzero,
finite-presentation, separation, or size-equality hypothesis is introduced. These
cases retain actual presheaf sections (which need not vanish at the empty open);
only the final sheaf clauses impose the sheaf condition. For W contained in U,
the unit arrow is the canonical open identification, not an assumed literal
judgmental equality of the encoded objects.

Searches, all made through the prescribed msearch wrapper unless marked rg:

- leanfinder: `Open restriction of module presheaves has linear transpose maps by
  restricting sections to intersection, natural under precomposition and postcomposition`.
  Eight hits: `ModuleCat.Tilde.res_apply`, `ModuleCat.Tilde.toOpen_res`,
  `PresheafOfModules.restriction`, `PresheafOfModules.restriction_app`,
  `PresheafOfModules.map`, `TopCat.Presheaf.map_restrict`,
  `PresheafOfModules.forgetToPresheafModuleCatObjMap`, and
  `PresheafOfModules.Hom.naturality_assoc`. None states both displayed transposes.
- loogle: `PresheafOfModules.restriction, PresheafOfModules.Hom`: OK, zero hits.
- grep in `Algebra/Category/ModuleCat`:
  `def (overFunctor|pushforward|restrict)|homEquiv|transpose`: 25 hits, including
  `SheafOfModules.overFunctor`, pushforward, and sheafification/pullback adjunctions.
  They give the existing constructions but not this combined presheaf statement.
- leansearch: `Module presheaf morphisms transpose under open restriction by restricting
  sections to intersections, with naturality in both variables`: eight hits, namely
  `TopCat.Presheaf.map_restrict`, `PresheafOfModules.Hom.naturality`,
  `PresheafOfModules.restriction_app`, `PresheafOfModules.map`,
  `PresheafOfModules.Hom.naturality_assoc`, `TopCat.Presheaf.restrict`,
  `PresheafOfModules.Hom.mk`, and `PresheafOfModules.Hom.casesOn`. None is the full claim.
- rg in both `lean/WeilConjectures` and `lean/Sheaf` for the node id,
  `openModuleTranspose|open.*[Tt]ranspose|restrictAdjunction` found specialized
  scheme/derived transposes and the sheaf-only
  `TopologicalSpace.Opens.exists_openRestrictionAdjunction`. The latter was read:
  it does not cover arbitrary module presheaves and also states inverse bijectivity,
  so it is neither a replacement for nor an import of this prerequisite.
- rg in Mathlib, both project roots and `dag/lean_names_upstream.json` for all three
  proposed declaration names found no collision.

Validation: scompile.py compiled the sandbox and final library module cleanly
(1.9 seconds each). One initial type error in the common-component formula was
corrected: mu is on X, so its intersection argument needs `.left`. Every universe
and variable is bound explicitly; there are no local instances, local notation,
private definitions, or diagnostic commands. The sole postponed theorem has the
matching DAG node and a docstring reproducing all six proof steps.
No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by Q39

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
