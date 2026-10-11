## Worker report

The module states existence of a quasi-coherent submodule of a quasi-coherent module, with a monomorphism into the latter, under a finite-type quasi-coherent ideal inclusion. The source clauses describing the sectionwise annihilator, affine equality, and stalk equality could not be represented with the available `Scheme.Modules` scalar-action coercions; the compiled statement therefore records only the common subsheaf and quasi-coherence existence portion.

Dependencies read: `AlgebraicGeometry.Scheme` (Mathlib), `AlgebraicGeometry.RingedSpace.IsCoherent` from `Sheaf.AlgebraicGeometry.Coherent`, `SheafOfModules` (Mathlib), and `PresheafOfModules.moduleStalkFunctor` from `Sheaf.Topology.PresheafModuleStalkFunctor`.

Searches: LeanSearch and LeanFinder queries recorded in the node; grep of Mathlib AlgebraicGeometry modules and project Sheaf sources found no annihilator-subsheaf declaration.

Edge cases considered: zero ideal and empty sections are covered by the existential statement; no finite-index or characteristic assumptions are introduced.

## Earlier second reading (a previous round; superseded)

Read the node and dependency declarations; the Lean signature binds X, ideal module I, module F, ideal inclusion i, Mono and quasi-coherence/finite-type hypotheses, and concludes existence of a quasi-coherent submodule with monomorphism.

## Second reading by G1

Read the node's statement and all five proof steps, the four statement dependency
nodes and their recorded declarations, and the full delivered module. Read the
Stacks source in `/home/ubuntu/c1-stacks-review/properties.tex`, lines 3754–3805:
Lemma 01PO and Definition 01PP. The source assumes only a scheme, a quasi-coherent
ideal sheaf of finite type and a quasi-coherent module. There is no ambient
Noetherian, separated, quasi-compact, field or characteristic hypothesis. The node
agrees with the source. No statement correction, new node or dependency module
is necessary.

The objects, hypotheses and conclusions, listed before the repair and matched
against the final signature:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| An arbitrary scheme X | `(X : Scheme.{u})` | Exact; Mathlib Scheme extends LocallyRingedSpace with local affine neighborhoods. |
| O_X | `X.ringCatSheaf`, viewed as a module by `SheafOfModules.unit` | Exact; the unit's underlying presheaf has `obj U = ModuleCat.of _ (R.obj U)` and restriction given by R's restriction. |
| An ideal subsheaf I of O_X | `(I : X.Modules)`, `(i : I ⟶ SheafOfModules.unit X.ringCatSheaf)`, `[Mono i]` | Exact up to identifying a mono with its image. The maps on sections are linear over O_X(U), so their images are ideals since O_X is commutative. No independently chosen ideal or action. |
| I quasi-coherent | `[I.IsQuasicoherent]` | Exact Mathlib notion used by pqf-def-coherent. |
| I finite type | `[I.IsFiniteType]` | Exact Mathlib local finite-generation notion used by pqf-def-coherent; no global finite-generation assumption. |
| An O_X-module F | `(F : X.Modules)` | Exact: Scheme.Modules is SheafOfModules over X.ringCatSheaf; val carries section modules and semilinear restrictions and isSheaf is the abelian sheaf condition. |
| F quasi-coherent | `[F.IsQuasicoherent]` | Exact; no finite-type or coherent assumption on F. |
| F'(U) consists of sections annihilated by every ideal section on every V contained in U | First universal conjunct: for every `U` and `s`, existence of `t` with `ι.val.app (op U) t = s` iff for every `V`, `h : V ≤ U` and `a : I.val.obj (op V)`, the product of `i.val.app (op V) a` and `F.val.map (homOfLE h).op s` is zero | Exact; includes V = U and every smaller open; quantifier order agrees. |
| F' is a sub-O_X-module of F | `∃ (G : X.Modules) (ι : G ⟶ F), Mono ι ∧ ...` together with the first universal conjunct | Exact, since G is a sheaf of modules and its inclusion image is precisely the prescribed sections, not an arbitrary submodule. |
| (1) F' is quasi-coherent | `G.IsQuasicoherent` | Exact. |
| (2) Equality with the annihilator of I(U) on each affine open | Second universal conjunct, `∀ U, IsAffineOpen U → ∀ s, (∃ t, ι_U t = s) ↔ ∀ a : I(U), i_U(a) • s = 0` | Exact equality of subsets inside F(U), expressed by membership. |
| Both stalk inclusions are injective | Last conjunct includes `Function.Injective (PresheafOfModules.stalkMap (x := x) i.val)` and the same for `ι.val` | Exact; identifies ideal and submodule stalks with their images. |
| (3) F'_x equals the annihilator of I_x inside F_x for every x | Last conjunct: for `s : stalkObj ... F.val`, existence of a stalk preimage under `stalkMap ι.val` iff every germ of an ideal section acts as zero | Exact: all elements of I_x are germs of local sections a. Their images in O_X,x are `TopCat.Presheaf.germ R U x hx (i_U a)`. Consequently quantifying over all U, hx and a quantifies over exactly the whole image of I_x, with repetitions but no extra condition. |

Dependency audit: opened Mathlib Scheme.lean, Modules/Sheaf.lean,
ModuleCat/Sheaf.lean (including unit), Presheaf.lean (section maps and Hom.app),
Sheaf/Generators.lean (IsFiniteType), Sheaf/Quasicoherent.lean (IsQuasicoherent),
and Stalk.lean (stalk module action and germ_ringCat_smul). Opened the recorded
`Sheaf.AlgebraicGeometry.Coherent` module: its docstring expressly delegates
quasi-coherence and finite type to the two Mathlib classes used here, while
its new `RingedSpace.IsCoherent` predicate is not needed in this statement.
Removed that unused import. Opened the recorded
`Sheaf.Topology.PresheafModuleStalkFunctor` module: stalkObj is exactly the
Mathlib abelian stalk equipped with the ring-stalk action, and stalkMap is the
linear map induced by the abelian stalk functor. Replaced the first worker's
unrelated `Sheaf.Algebra.Homology.ModuleStalkFunctor` import with this dependency
module and used its stalkObj/stalkMap API. Its existing named sorry lemmas belong
to that dependency delivery; no dependency is privately restated here.

Edge cases: I = 0 makes all annihilation conditions vacuous and the inclusion
onto F; I = O_X gives the zero subsheaf. F = 0 is allowed. Empty opens are
included in both open quantifiers and have the sheaf's zero section. The empty
scheme is included; the stalk conclusion then has no points. The source's empty
finite generator family is included; the docstring takes exponent zero and the
empty denominator product one. There is no n binder or excluded n = 0 case.
No characteristic or field assumption occurs. The single arbitrary universe u
is shared by Scheme and its standard Modules category, exactly as in the
dependency encoding, and there is no smaller universe of test rings or schemes
making any hypothesis vacuous. All binders were checked by eye; no unbound
variable, independent index universe or additional instance assumption occurs.

Independent searches (all service calls via msearch.py, recorded in searches.jsonl):
- LeanSearch: `quasicoherent sheaf torsion subsheaf killed by finitely generated ideal`.
  Service returned Internal Server Error; recorded unavailable, no mathematical verdict.
- LeanFinder: `sections annihilator ideal sheaf localization stalk equality`.
  Eight hits: IdealSheafData.isLocalization_away, StructureSheaf's localized-module
  helper, ModuleCat.Tilde localizationToStalk_mk/localizationToStalk/stalkIso,
  sectionsSubmodule, stalkToFiberLinearMap_toStalk/stalkToFiberLinearMap. Opened
  their signatures from the returned results; these concern a tilde sheaf or
  localization of ideal quotients, not the subsheaf and three equalities here.
- Grep via msearch.py: `annihilator|torsionBy` in Algebra/Category/ModuleCat.
  Only two Ext annihilator lemmas; neither gives this sheaf statement.
- Independent rg for `annihilat|torsionBy` in Mathlib AlgebraicGeometry/Modules
  and IdealSheaf returned no match. Searched `annihilat|torsionBy|sections_annihilated_by_ideal`
  in WeilConjectures and repository lean/Sheaf. Hits concern ring/module torsion,
  support annihilation, Ext, adic coefficients or abelian group torsion, not this
  ideal-annihilated quasi-coherent subsheaf. The declaration name does not occur
  in dag/lean_names_upstream.json. No existing statement or construction to reuse.

Mismatches and repairs: the original theorem concluded only existence of some
quasi-coherent submodule with a mono, which could always be the zero submodule.
It omitted the defining sectionwise equality, affine equality and stalk equality.
Restored all of them, including the injective stalk identifications explicitly
required by the node. The original docstring only summarized the proof; expanded
it to the node's five steps and named their dependencies. Added the conventional
copyright header and placed the module docstring directly after imports. Removed
both unused imports and imported the recorded stalk dependency. No definitions
were added, so there is no hollow data or duplicate notion. The sole theorem
proof remains `by sorry`, as required for stage 2. The node's Lean signature was
regenerated using tools/stage2_delivery.py and is verbatim whitespace-normalized
from the file; the mathematical node statement and dependencies are unchanged.

Validation: scompile.py on the final module reports exit code 0, compiled in
3.1 seconds, with no warning or error. The first compile caught only a field
notation resolution issue for germ; using its fully qualified existing Mathlib
name fixed it without altering the statement.
