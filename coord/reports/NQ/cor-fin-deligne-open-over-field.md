## Worker report

The module Sheaf.AlgebraicGeometry.OpenDirectImageOverField states
AlgebraicGeometry.Etale.isBoundedConstructible_rightDerivedLowerStar_primeSheaf_of_isOpenImmersion.
Its only theorem has proof `sorry`; it introduces no definitions. The node statement
and dependency lists are unchanged.

Hypothesis and conclusion correspondence:

- The field k is `(k : Type u) [Field k]`.
- The prime implicit in F_l is `(l : ℕ) [Fact l.Prime]`; its characteristic restriction
  is `(hl : l ≠ ringChar k)`. This includes characteristic zero.
- X and Y are arbitrary `Scheme.{u}` with their `Over (Spec (.of k))` structures.
  Each structure morphism has `LocallyOfFiniteType` and `QuasiCompact`, exactly
  finite type in the recorded scheme conventions.
- The open immersion is `(j : X ⟶ Y) [IsOpenImmersion j]`; the condition
  `[j.IsOver (Spec (.of k))]` says it is a morphism of the given k-schemes.
- F is a sheaf on X.smallEtaleTopology with values in
  `ModuleCat.{u + 1} (ULift.{u + 1} (ZMod l))`. The ULift changes only universe size:
  it is the prime field F_l through its canonical ring equivalence with ZMod l.
  The fixed coefficient universe is that of the recorded derived-category dependency.
- Constructibility is `(hF : Scheme.IsConstructibleEtaleModuleSheaf F)`, the recorded
  finite locally closed stratification notion, without a stalkwise replacement.
- `(_root_.DerivedCategory.singleFunctor _ 0).obj F` is F placed in degree zero.
  `rightDerivedLowerStar ... j` applied to it is the ordinary total derived direct
  image Rj_*F, with no completion or pro-etale change of categories.
- `DerivedCategory.isBoundedConstructible ... Y` is exactly membership in D^b_c:
  every cohomology sheaf is constructible, and all vanish outside some integer
  interval [a,b] with a ≤ b. No Tor amplitude or base-change assertion is added.

Recorded dependency declarations read and used:

- Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes:
  AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible.
- Sheaf.AlgebraicGeometry.DerivedCategories, via the public upstream import
  WeilConjectures.SixFunctors.Etale.Derived.Coefficients:
  AlgebraicGeometry.Etale.DerivedCategoryModule; the underlying category is
  DerivedCategory of etale module sheaves. Mathlib's DerivedCategory.singleFunctor
  places F in degree zero.
- def-weil-pbc-scheme-conventions is an explicit convention record with no module or
  declaration. Its finite-type and open-immersion conventions are rendered with
  Mathlib LocallyOfFiniteType, QuasiCompact and IsOpenImmersion.
- Constructibility, publicly imported by BoundedConstructibleComplexes, is
  AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf in
  Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf.
- Ordinary derived direct image is the existing
  AlgebraicGeometry.Etale.rightDerivedLowerStar in
  WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence; its full definition
  applies Functor.rightDerivedFunctor to the existing Etale.lowerStar.

The sole proof dependency thm-fin-deligne-generic-open has no Lean record or module;
there is consequently no proof import to add. Its absence does not prevent stating
this corollary. The docstring reproduces the two proof steps: verification of all
hypotheses over Spec k, then identification of its nonempty base open with Spec k.
The generic theorem's stronger exchange conclusion is not used.

Edge cases checked: empty X and/or Y and the zero sheaf are allowed; the empty
partition in constructibility causes no extra nonemptiness requirement. For the
identity open immersion the result reduces to bounded constructibility of a
constructible sheaf in degree zero. No separatedness, algebraic closedness,
perfection or finite cohomological dimension of k is assumed. The prime hypothesis
excludes l = 0 and l = 1, precisely as required for the notation F_l. All universes
and variables are explicitly bound. No statement fault or dispute was found.

Searches for existing declarations:

- msearch.py leanfinder: "Higher direct image under an open immersion of finite type
  schemes over a field preserves bounded constructible etale sheaves" returned eight
  hits, including Scheme.Hom.isConstructible_image, module restriction and faithful
  pushforward; none states this sheaf corollary.
- msearch.py loogle: `AlgebraicGeometry.IsOpenImmersion, "derived"` returned zero hits.
- msearch.py grep: `deligne|boundedConstructible.*[Oo]pen` in Mathlib/AlgebraicGeometry
  returned only the unrelated elliptic-curve bibliography.
- rg of the upstream WeilConjectures and project lean/Sheaf for the exact blueprint
  id and Deligne/open-image names found OpenDirectImageFiniteCoefficients and upstream
  Derived/Finiteness/DirectImage. Their full signatures concern arbitrary allowable
  coefficient rings and bounded constructible complexes, rather than this prime-field
  sheaf statement; the upstream predicate also differs from the recorded predicate.
  Read both modules; neither is an exact existing declaration for this node.
- Read UpperLowerStarCoherence, DerivedCategories, BoundedConstructibleComplexes,
  IsConstructibleEtaleModuleSheaf, and the source blueprint node itself.

Validation: scompile.py NQ cor-fin-deligne-open-over-field compiled the delivered file
on the server cleanly, within the prescribed per-file time limit. No local compiler
or global build was run.

## Second reading by NQ

I independently read the node copy, OpenDirectImageOverField.lean, the source
blueprint corollary and its generic-open theorem, all three statement-dependency
nodes and their recorded declarations. The cited source is the blueprint markdown,
not a Stacks tag: its corollary and generic theorem impose no ambient separatedness,
perfectness or algebraic-closedness assumption. The generic theorem's Noetherian-test-
base condition concerns its additional exchange conclusion, which this corollary
does not claim. The specialization to Spec k meets its integral finite-type-base
hypothesis. No statement_change is present or needed.

Object, hypothesis and conclusion inventory, matched in order:

1. A field k: `(k : Type u) [Field k]`. Verdict: exact; k is arbitrary.
2. Prime-field coefficients F_l with characteristic different from l:
   `(l : ℕ) [Fact l.Prime] (hl : l ≠ ringChar k)` and the coefficient ring
   `ULift.{u + 1} (ZMod l)`. Verdict: exact. ZMod of a prime is F_l; ULift
   carries its existing ring structure, changing size only. No invertibility
   assumption stronger than the characteristic condition is introduced.
3. Finite-type k-schemes X and Y: `{X Y : Scheme.{u}}`, their respective
   `Over (Spec (.of k))` instances, and `LocallyOfFiniteType` plus `QuasiCompact`
   on both structure maps. Verdict: exact. I read the scheme-conventions node;
   it explicitly specifies this conjunction, as does Mathlib's FiniteType module.
4. An open immersion of these k-schemes: `(j : X ⟶ Y)` with
   `[j.IsOver (Spec (.of k))] [IsOpenImmersion j]`. Verdict: exact. IsOver
   expresses compatibility with the two given structure morphisms; there is no
   assumption that j is proper, affine or dense.
5. A constructible F_l-sheaf on X: `F : Sheaf X.smallEtaleTopology
   (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod l)))` and
   `hF : Scheme.IsConstructibleEtaleModuleSheaf F`. Verdict: exact. I opened
   IsConstructibleEtaleModuleSheaf: it requires a finite locally closed
   constructible stratification and etale local trivializations with finite module
   values, precisely the constructible-complexes dependency's sheaf notion.
6. The ordinary derived image Rj_*F: `rightDerivedLowerStar ... j` applied to
   `(_root_.DerivedCategory.singleFunctor _ 0).obj F`. Verdict: exact. In
   UpperLowerStarCoherence the functor is the total right derived functor of
   Etale.lowerStar; Coefficients defines DerivedCategoryModule as the ordinary
   DerivedCategory of these very module-valued sheaves. This is neither a completed
   category nor a pro-etale category.
7. Membership in D^b_c(Y,F_l): `DerivedCategory.isBoundedConstructible ... Y`
   of that object. Verdict: exact. I opened BoundedConstructibleComplexes: all
   integer cohomology sheaves satisfy the same constructibility predicate, and
   there exist integers a ≤ b outside which they are zero. Both clauses are
   present; no Tor, exchange or support conclusion was added. All inputs precede
   this conclusion, with no extra choices or reordered existential quantifiers.

Edge cases: X may be empty; Y may be empty (then an open immersion forces X empty);
F may be zero; j may be the identity. None is excluded by a binder or nonemptiness
instance. There is no index set in this statement; the constructibility dependency
allows the empty stratification. The degree-zero embedding explicitly includes
cohomological degree 0, and the conclusion ranges over every integer, including
negative degrees. l = 0 and l = 1 are excluded exactly by primality; characteristic
zero and every positive characteristic different from l remain allowed. The scheme
and field universe u is arbitrary and may be chosen to contain all input data;
finite constant values live in the prescribed u+1 coefficient universe. No equality
of site object and morphism universes or extra smallness binder was imposed.

Independent H4 searches used different wording from the first reader:

- msearch LeanFinder: "Etale cohomology of an open subscheme over a field has
  constructible higher pushforwards and vanishes in high degrees". Eight hits,
  including Scheme.etaleTopology, Scheme.smallEtaleTopology and etale-locus results;
  none states the corollary.
- msearch Loogle: `"rightDerivedLowerStar"`. Zero hits.
- rg on Mathlib/AlgebraicGeometry, upstream WeilConjectures, and project lean/Sheaf
  for open/direct-image wording and for
  `boundedConstructible.*(isOpenImmersion|prime)` and
  `isBoundedConstructible.*(isOpenImmersion|prime)`. I opened the relevant signatures
  in upstream Derived/Finiteness/DirectImage and project
  OpenDirectImageFiniteCoefficients. The upstream sheaf theorem uses
  IsConstructibleSheaf and boundedConstructible, not the recorded finite-constant-
  stratification predicate; the project theorem quantifies over general allowable
  finite rings and bounded constructible complexes. Neither is the exact statement
  of this prime-field sheaf node. No duplicate definition or declaration was found.

No new definition node or dependency module is delivered. The convention dependency
intentionally has no declaration; the two category/constructibility modules are
publicly imported and their interfaces are usable. The sole proof dependency,
thm-fin-deligne-generic-open, has no recorded Lean module, so there is no missing
proof import to add. Its two specialization steps are both reproduced in the
statement docstring, with source and blueprint id. The theorem's sole proof is
`sorry`; there are no definitions, auxiliary proofs or unbound universe variables.
The node's lean.statement equals the source signature verbatim. I found no mismatch
and preserved the Lean module and node unchanged. Only this independent review was
added to the report. Server scompile validation is recorded below.

Validation: the second reader ran scompile.py on the delivered module; server
compilation exited 0 without warnings (library file: 1.9 seconds). A textual
assertion confirmed lean.statement is verbatim the theorem signature.
