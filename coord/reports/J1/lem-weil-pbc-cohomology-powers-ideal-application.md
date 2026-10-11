## Worker report

The main module `Sheaf.AlgebraicGeometry.CohomologyPowersIdealApplication` states
`AlgebraicGeometry.cohomology_powers_ideal_application`, the two uniform bounds of
Stacks 02OA (2), (3). Its proof is `sorry`. The node's statement is unchanged.
Source read: https://stacks.math.columbia.edu/tag/02OA (the local literature checkout
has no coherent.tex). The module docstring gives all eight proof steps of the DAG node.

Hypothesis and clause correspondence:

- Commutative Noetherian A: `(A : Type v) [CommRing A] [IsNoetherianRing A]`.
- Ideal I of A: `(I : Ideal A)`; no nonzero or proper-ideal restriction.
- Proper f : X → Spec A: `{X : Scheme.{v}}`, `(f : X ⟶ Spec (CommRingCat.of A))`,
  `[IsProper f]`. No independent hypothesis on X is added.
- The extended ideal is `baseIdealSheaf f I`: `I` is transported to Γ(Spec A)
  using `Scheme.ΓSpecIso.inv`, put into `IdealSheafData.ofIdealTop`, then pulled
  back by the recorded `IdealSheafData.comap f`. These are the associated ideal
  sheaf and its extension I O_X, not a separately supplied arbitrary ideal.
- Coherent O_X-module: `(F : X.Modules)` and
  `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`.
- Power convention: `idealPowerModule` is exactly F at zero. At positive n it is
  the recorded `Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F`.
- The canonical inclusions for k ≥ n are `idealPowerModuleInclusion ... h`.
  They are chosen from the named existence theorem asserting the factorization
  through the inclusions into F. Both inclusions are monic, so that equation
  uniquely specifies the inclusion: the choice supplies no arbitrary map.
- Fixed q ≥ 0: `(q : ℕ)`; no negative cohomology is included or positive degree excluded.
- M_n: `idealPowerCohomology f I F q n` evaluates the recorded
  `RingedSpace.moduleCohomology X.toRingedSpace q` on the power module and restricts
  scalars along `((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom`.
  Thus the A-action is precisely the action through global sections stipulated
  by the node. This is a composition of existing functors, not a new cohomology.
- μ_(k,n): `idealPowerCohomologyMap f I F q h` is that same functor applied to
  the canonical inclusion of the power modules; its `.hom` is an A-linear map.
- One nonnegative integer constant for both parts: `∃ c : ℕ, (...) ∧ (...)`.
- Part (a): all `(n m : ℕ)` with `c ≤ n + m`; `LinearMap.range` of μ_(n+m,n)
  is bounded by `I ^ (m - (c - n)) • (⊤ : Submodule A M_n)`.
  Natural subtraction `c - n` equals max(0,c-n); under n+m ≥ c it is ≤ m,
  so the exponent is exactly m-e and cannot truncate an intended negative exponent.
- Part (b): all `n : ℕ` with `c ≤ n`; equality of `LinearMap.ker` of μ_(n,0)
  and μ_(n,n-c), using `Nat.zero_le n` and `Nat.sub_le n c` as index proofs.

Recorded dependencies used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (read signature and docstring).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
  Its locally-finite-type formulation is equivalent here because universally closed
  implies quasi-compact, as the dependency's record explains.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`:
  `AlgebraicGeometry.Scheme.IdealSheafData.comap` (read full declaration/docstring).
- `Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`
  (finite type and finite-type kernels on every open).
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`: the notation (0) uses the shared
  product/power definitions imported from `Sheaf.AlgebraicGeometry.IdealModuleProductStalk`:
  `Scheme.idealModuleProduct`, `Scheme.idealModuleProductι`, `Scheme.idealSheafPower`.
  No completion object is involved in this lemma.
- `Sheaf.Paper.PQFCohomology`: its declaration
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages` identifies the cohomology
  functors with `RingedSpace.moduleCohomology` in
  `Sheaf.Topology.RingedSpaceModuleCohomology`, which the new system module imports.
  Read both full signatures/docstrings. The delta-functor and direct-image assertions
  are not additional premises of this application.
- New dependency `def-weil-pbc-ideal-power-cohomology-system`:
  `Sheaf.AlgebraicGeometry.IdealPowerCohomology`,
  `AlgebraicGeometry.idealPowerCohomologyMap` and its accompanying explicit definitions.

Edge cases checked before writing: q=0 is allowed; n=0 uses exactly F, and part (a)
then gives I^(m-c) H^q(X,F) for m ≥ c. When n ≥ c, c-n=0 and the exponent is m.
At n=c the right-hand kernel in (b) is also Ker(μ_(c,0)). At c=0 part (b) says
μ_(n,0) is injective because μ_(n,n) is the identity. At m=0 part (a) bounds the
identity image by I^0 M_n=M_n. Zero module, zero ideal, unit ideal, zero ring,
and empty scheme are not excluded. Index universes do not introduce test objects
or a vacuous quantifier. All universes and binders are explicit.

Searches for existing declarations (all msearch calls use group J1 and this item):

- LeanFinder: `Artin Rees bounds for cohomology of powers of an ideal times a coherent
  sheaf on a proper scheme`: localCohomology and algebraic Artin–Rees only,
  no sheaf-cohomology image/kernel bound.
- Loogle: `CategoryTheory.Sheaf.H, Ideal` and `Ideal, CategoryTheory.Sheaf.H`: zero hits.
- Mathlib grep: `cohomology.*[Pp]ower|[Pp]ower.*cohomology` in AlgebraicGeometry: zero hits.
- Source and landed-module rg: powers/cohomology patterns identify affine Čech lemmas,
  unrelated tensor powers, and the existing ideal-module products, but no bounds or
  canonical power-cohomology transition maps.
- Source rg for the item id: zero hits.
- Name collision rg over Mathlib, WeilConjectures and lean/Sheaf for all new declaration
  stems (idealPowerModule, idealPowerCohomology, baseModuleCohomology, baseIdealSheaf,
  cohomology_powers_ideal_application): zero hits.
- Extra-node searches are detailed below and recorded as returned in its mathlib_searches.

No statement dispute or correction. No dependency record needed replacement.

## New nodes

`def-weil-pbc-ideal-power-cohomology-system` supplies the missing canonical transition
maps for the setup of Stacks 02OA, with the exact level-zero convention and actual
A-module scalar restriction. It does not duplicate the shared ideal products, powers,
extension, or derived cohomology definitions: its helper definitions compose these,
and its genuinely missing operation is factoring the power inclusions and applying
cohomology. The node cites the existing three notions on which it is built. Its eight
named declarations have full source docstrings. The only auxiliary `sorry` is the named
`idealPowerModule_inclusion_exists`, whose source and complete proof (containment of
product image subsheaves and monicity for uniqueness) are in its docstring; the data of
all definitions are explicit, with the canonical map chosen from this existence theorem.
This follows the contract's allowance for data chosen from a named theorem.

Search first: `tools/blueprint_refs.py search 'cohomology powers'` returned zero blueprint
nodes. DAG rg for canonical inclusion/transition powers found no node defining these maps;
the application and Rees-finiteness nodes use them in prose. The completion dependency
only defines quotient maps (formalModuleQuotientMap), not inclusion maps between products.
Mathlib/source/landed module name searches found no such operation. LeanSearch query
`canonical inclusion of powers of an ideal times a sheaf of modules` returned service
unavailable (Internal Server Error); this is recorded as unavailable. LeanFinder query
`canonical transition maps on cohomology of powers of an ideal sheaf times a module`
returned localCohomology, adic-completion quotient transitions, and algebraic ideal-power
quotient maps, none defining sheaf product inclusions or their cohomology. Mathlib grep
`idealModuleProduct|idealSheafPower|idealPowerModule|idealPowerCohomology` returned no hits.
The existing project product definitions were read and reused instead of being copied.

## Second reading by J1

I independently opened both delivered nodes and both Lean modules, each recorded
statement dependency, and the declarations used below. I read Stacks coherent.tex
from the section `section-theorem-formal-functions` through the statement and proof
of `lemma-cohomology-powers-ideal-application` (02OA). The repository has no local
Stacks checkout; the fetched upstream TeX is retained only in this sandbox's scratchpad.
The section introduces ideal products as images of multiplication; it adds no
standing assumption beyond the hypotheses explicitly present in 02OA. No statement
correction is present or needed.

Object/hypothesis/conclusion checklist, written from the node before comparison:

1. A commutative Noetherian ring A: `(A : Type v) [CommRing A]
   [IsNoetherianRing A]`. Exact: the abbreviation is Noetherian as an A-module,
   equivalent to finite generation of every ideal. No field/domain assumption.
2. An ideal I in A: `(I : Ideal A)`. Exact, including zero and unit ideals.
3. A scheme X and proper f to Spec A: `{X : Scheme.{v}}`,
   `(f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]`. Exact: the recorded
   class gives separated, universally closed and locally finite type; universally
   closed supplies quasi-compactness and therefore finite type. There is no extra
   independent Noetherian/separated/finite-type assumption on X.
4. The extended ideal I O_X: `baseIdealSheaf f I`. Exact: `ΓSpecIso.inv` maps
   A to global sections of Spec A, `ofIdealTop` associates the ideal sheaf,
   and `IdealSheafData.comap f` extends it. I read comap's pullback-kernel
   definition: the base change of the closed subscheme cut out by I cuts out
   I O_X. On each affine open Spec B its ideal is I B, as the node requires.
5. A coherent O_X-module F: `(F : X.Modules)` and
   `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`. Exact: I read
   IsCoherent's finite-type condition and finite-type kernels on all opens;
   it does not replace coherence by local freeness or finite presentation.
6. Powers as subobjects with level zero F: `idealPowerModule (baseIdealSheaf f I)
   F n`. Exact: zero is literally F and positive levels use the shared
   `idealSheafPower` and `idealModuleProduct` image of tensor multiplication.
   I read their recursive definitions and `idealModuleProductι`. Powers of the
   extended ideal give the source's image of f^*(I^n)~ times F, since on affine
   opens both ideals are I^n B. The level-zero inclusion is literally the identity.
7. A fixed q >= 0: `(q : ℕ)`. Exact, with q outside the existential constant.
8. M_n as H^q of the power module, with the specified A-action:
   `idealPowerCohomology f I F q n`. Exact: `baseModuleCohomology` composes
   the recorded `RingedSpace.moduleCohomology` (right derived global sections)
   with `ModuleCat.restrictScalars` along `ΓSpecIso.inv ≫ f.appTop`.
   I read restrictScalars' object and map definitions: scalar a acts through
   its image in global sections, and maps retain their underlying additive maps.
9. Canonical maps mu_(k,n), for k >= n: `idealPowerCohomologyMap f I F q h`.
   Exact: it applies that same functor to `idealPowerModuleInclusion`.
   The existence theorem specifies the factorization through the inclusions into F.
   These are image inclusions (or the identity at zero), hence monic; the
   factorization determines a unique map. Classical.choose therefore picks the
   canonical map, not a freely chosen transition system.
10. One nonnegative integer c for both conclusions: `∃ c : ℕ, (...) ∧ (...)`.
    Exact, with no requirement c > 0 and no dependence on n or m.
11. Image bound for every n,m >= 0 with n+m >= c: the first `∀ (n m : ℕ)`
    and `c ≤ n + m` premise. `Nat.le_add_right n m` specifies mu_(n+m,n);
    `LinearMap.range ... ≤ I ^ (m - (c - n)) • ⊤` is the required containment
    in I^(m-e) M_n. Exact: c-n in naturals is max(0,c-n); the premise ensures
    e <= m, so no integer exponent is lost to truncated subtraction.
12. Kernel equality for every n >= c: the second `∀ n : ℕ`, `c ≤ n`
    premise, and equality of `LinearMap.ker`. `Nat.zero_le n` selects mu_(n,0)
    and `Nat.sub_le n c` selects mu_(n,n-c). Exact: both kernels are submodules
    of the very same M_n, not just abstractly isomorphic groups.

Edge cases: n=0 uses F exactly; the image bound then has exponent m-c for m>=c.
At n>=c the image exponent is m. At n=c the two kernel maps coincide. At c=0,
mu_(n,n) is the canonical identity by uniqueness, so (b) asserts injectivity
of mu_(n,0). At m=0, the premise forces n>=c and the image bound is by I^0 M_n.
Zero F, empty X, zero A, I=0, and I=A are all admitted. There is no index set to
assume nonempty, no characteristic restriction, and no negative degree in the node.
The single arbitrary universe v puts A, X and its module sheaves in the same
ambient universe; it contains no test-object quantifier or accidental smallness
hypothesis. Universes u/v and all term binders are explicitly declared.

New-node reading (H12): `def-weil-pbc-ideal-power-cohomology-system` is the
source's setup, not an additional finiteness theorem. Its general J and F are
rendered by `X.IdealSheafData` and `X.Modules`; the module does not assume F
coherent or X Noetherian to define the maps. All eight declarations implement
its stated construction. Its three cited definition dependencies are reused,
not copied. I verified definition/split status, chapter/unit, fresh id, created
record, ancestor/via, empty proof/proof_deps, null mathlib_match, none audits,
three search kinds, full Lean record, and the item's dependency edge. There are
no dependency replacement modules. The auxiliary existence theorem has a source
and a natural-language containment proof; all definitions have explicit data
and only this named theorem supplies a postponed proof for a choice.

Independent searches (different wording from the first reading):

- LeanFinder: `Images and kernels of cohomology transition maps for adic filtrations
  on proper schemes`. Hits were localCohomology, AdicCompletion.map_exact,
  adic quotient transitions and ring-module filtration facts; none states 02OA.
- Loogle: `Ideal, LinearMap.ker`. Twelve ring/module kernel facts, including
  Submodule.comap_smul_top_of_surjective and completion evaluation kernels;
  none concerns ideal-product sheaf cohomology on a proper scheme.
- LeanSearch: `sheaf cohomology of ideal power inclusions on a proper scheme
  uniform kernel image bound`. Service unavailable (Internal Server Error),
  recorded as unavailable rather than evidence of absence.
- LeanFinder for the new notion: `Canonical inclusions of nested image subsheaves
  from powers of a quasi coherent ideal and induced cohomology maps`. Hits
  IdealSheafData.inclusion_comp and glueDataObjHom concern closed subscheme
  morphisms in the opposite direction, not inclusions of module images times F;
  localCohomology and Ideal.powQuotSuccInclusion are also different objects.
- rg on Mathlib AlgebraicGeometry, WeilConjectures and landed lean/Sheaf with
  `cohomology.*[Pp]ower|[Pp]ower.*cohomology|idealPowerModule|idealPowerCohomology`
  found no matching declaration. Additional `power.*[Ii]ncl|[Ii]ncl.*power`,
  `restrictScalars.*appTop`, and `ΓSpecIso.*inv` searches confirmed that existing
  ingredients concern scalar restriction or quotient/reduction maps, not this
  system. `tools/blueprint_refs.py search 'ideal power cohomology'` returned zero;
  DAG concept searches found the application, completion and formal-function
  uses but no definition of these canonical module inclusion/cohomology maps.

H5/H6/H8/H9: no hollow definition, private declaration, local notation, local
instance, let/show statement binder, or unbound variable. Both theorem proofs
remain sorry. Every declaration and module has its source and blueprint id;
the main theorem's docstring follows all eight node proof steps, including
both generation bounds, their maximum, the two image cases and both kernel
containments. Both node Lean signatures match the files verbatim. No mathematical
mismatch was found; I changed only this report by adding the independent reading.

Validation: both delivery modules compiled together with scompile.py, dependency
first, in 2.0 seconds with exit 0 and no warnings.
