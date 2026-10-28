## Worker report

Restores `Sheaf.Paper.FiniteTorInternalHomAnyField` and states
`AlgebraicGeometry.Scheme.finiteTor_internalHom_constructible_anyField`, with `sorry`.
The former module was deleted as dead; the current node has `lean: null` and records
that deletion in `lean_removed`. `scompile.py --source` confirmed the module is absent.
No dependency node or mathematical statement is changed and no new definition is needed.
No repair note exists for this item.

Hypothesis and conclusion correspondence, read against the node:

- Arbitrary field: `(k : Type u) [Field k]`. No characteristic, perfection,
  separable-closedness or cohomological-dimension hypothesis is introduced.
- Prime invertible in k: `(l : ℕ) [Fact l.Prime] (_hl : IsUnit (l : k))`.
- Finite E/Q_l: `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. The recorded
  `Padic.coefficientExtensionRing l E n` is exactly the quotient of its recorded
  integer ring by the nth power of the ideal of its chosen uniformizer.
- Positive level: `(n : ℕ) (hn : 1 ≤ n)`. The same n and hn are used throughout.
- Separated finite-type k-scheme: `X : Scheme.{u}`, `X.Over (Spec (.of k))`,
  `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` of its structure morphism.
  The latter two together express finite type in the project's scheme convention.
- Constant A_X-modules on the small pro-etale site and their ordinary derived category:
  `K M : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)`.
  This uses the existing `ProEt.topology X` and constant sheaf of the canonical ULift
  of the coefficient ring, with module sections in universe u+1; the site retains
  object universe u+1 and morphism universe u.
- Bounded constructibility and finite Tor for each input: `_hK` and `_hM` are the
  recorded `WeilConjectures.finiteTorConstructible l E n hn X` predicates.
  Its definition is the conjunction of `intrinsicFiniteTorsionConstructible` and
  `HasFiniteProEtaleTorAmplitude`; the latter has one ordered integer interval
  for every degree-zero module sheaf, tested on all K-flat representatives.
- Ambient RHom: `derivedInternalHomOfUniverses.{u + 1, u, u}` at
  `ProEt.topology X` and `proEtaleConstantRing X A`, evaluated at `(op K, M)`.
  This is the recorded localization of the Hom complex with functorial K-injective
  replacement, rather than a Hom internal to a small constructible category.
- Conclusion D^b_c and finite stalks: the first conjunct is
  `intrinsicFiniteTorsionConstructible l E n hn X` of that exact object.
  Its definition is finite cohomological support and constructibility of each
  cohomology sheaf; the underlying stratification predicate requires finite stalks.
- Bounded constructible etale origin: the second conjunct quantifies an ordinary
  etale derived object L, requires `Etale.DerivedCategory.isBoundedConstructible`
  of L, and an isomorphism from its canonical
  `ProEtale.finiteCoefficientIntrinsicDerivedComparison` image to the same RHom.
  All finite instances here are passed explicitly from
  `Padic.finite_coefficientExtensionRing l E n hn`; they are derived facts, not
  added hypotheses. The ULift finiteness is `Finite.of_equiv` along `Equiv.ulift.symm`.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; its public coefficient-extension module
  provides `coefficientExtensionRing`, integers, uniformizer and ideal.
- The scheme-properties dependency is explicitly a convention node. Its named
  Mathlib interfaces are `AlgebraicGeometry.IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact` (the signatures/docstrings in the respective morphism modules).
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`
  and `ProEt.topology`, exactly the site's recorded declaration.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: public recorded
  `WeilConjectures.finiteTorConstructible` (defined in `FiniteTorAmplitude`).
- `Sheaf.Algebra.Homology.DerivedInternalHomMixedUniverses`: publicly exports
  `CategoryTheory.derivedInternalHomOfUniverses`, whose full signature/docstring
  was read in `DerivedInternalHomOfUniverses`. Its site and coefficient universes
  fit the intrinsic category directly, so the mixed-ring variant is unnecessary.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`:
  `AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicDerivedComparison`.
  Its ordinary-etale bounded-constructibility predicate is supplied by the already
  public imports of `FiniteTorAmplitudeSites`; no new notion is introduced.
- Recorded proof-dependency modules with declarations are imported privately,
  including `FiniteRingConstructibleDerivedOrigin`; the proof docstring spells
  out all eleven steps of the accepted node proof.

Source reading: extracted and read pp. 49--58 of the local Bhatt--Scholze PDF,
including Definition 6.5.1, its finite-coefficient comparison, Lemmas 6.7.2,
6.7.11 and 6.7.13. The finite-Tor assumptions preserve the source's perfect-on-strata
condition. No node correction or STATEMENT-DISPUTED finding is needed.

Edge cases checked before writing: empty X and either zero input yield zero;
n=1 is admitted, n=0 is expressly outside the node; characteristic zero and
imperfect positive-characteristic fields are admitted provided l is invertible.
For A=Z/l^2, the residue module can have infinite Tor dimension, so the input
finite-Tor conditions are retained rather than inferred from constructibility.
There is no assertion of finite Tor amplitude for the output.

Searches actually run through msearch.py:

- LeanFinder: “Derived internal Hom of bounded constructible finite Tor amplitude
  complexes over finite rings on schemes over arbitrary fields is bounded constructible”.
  Eight hits, all abstract derived-category cohomological bounds, none this theorem.
- Loogle: `derivedInternalHomOfUniverses, intrinsicFiniteTorsionConstructible`:
  zero hits, reporting the first identifier unknown to the Mathlib service.
- Mathlib grep: `constructib.*[Hh]om|[Hh]om.*constructib|finiteTor` in
  AlgebraicGeometry: three constructible-image/preimage hits in FinitePresentation,
  no derived Hom finiteness theorem.
- LeanSearch: “Derived internal Hom preserves bounded constructibility for finite Tor
  amplitude constructible complexes on schemes over any field”. Eight hits for
  exact-functor localization, homology and internally projective objects, no match.
- rg of `lean/Sheaf` and `lean/WeilConjectures` for finiteTor, internalHom and
  constructibility located the interfaces used above. The nearby
  `isBoundedConstructible_finiteTor_derivedHom_by_devissage` requires IsSepClosed k
  and uses etale endpoints, so it is not an exact attachment. Integral Hom theorems
  have different coefficient objects. Searches for the item id and exact former
  declaration found no current declaration. The source wrapper reports it absent.

Validation: scompile.py compiled sandbox and named-library presentations cleanly
(2.1 s and 2.0 s). Only the theorem proof is postponed; all variables and the single
universe are bound explicitly and autoImplicit is disabled.

## Second reading by NB

Independent second reading (maintainer cc review service, 2026-10-28), replacing the
author's self-audit recorded at the end of this section. Delivery 968873c2cac0.

Node statement as a list, with the Lean rendering and verdict:

1. Field k, arbitrary: `(k : Type u) [Field k]`; no characteristic, perfection,
   separable-closedness or cohomological-dimension instance. OK.
2. Prime ℓ invertible in k: `(l : ℕ) [Fact l.Prime] (_hl : IsUnit (l : k))`. OK.
3. E/Q_ℓ finite, R = O_E, ϖ, A = R/ϖ^n, n ≥ 1: `[Field E] [Algebra (Padic l) E]
   [FiniteDimensional (Padic l) E]`, `(n : ℕ) (hn : 1 ≤ n)`,
   `Padic.coefficientExtensionRing l E n` (the record of
   def-weil-l-adic-coefficient-extension). OK.
4. X separated finite type over k: `X.Over (Spec (.of k))`, `IsSeparated`,
   `LocallyOfFiniteType`, `QuasiCompact` of `X ↘ Spec (.of k)`, the Mathlib interfaces
   named by the convention node def-weil-scheme-morphism-properties. OK.
5. Small pro-étale site, constant ring A_X, ordinary derived category:
   `proEtaleDerivedCategory X A` (Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory:
   SheafOfModules over the constant `ULift A` ring sheaf on `ProEt.topology X`,
   standard derived category). OK.
6. K, M ∈ D^b_c(X,A) with finite Tor amplitude: `_hK`, `_hM :
   WeilConjectures.finiteTorConstructible l E n hn X _` = `intrinsicFiniteTorsionConstructible
   ⊓ HasFiniteProEtaleTorAmplitude` (Sheaf.Paper.FiniteTorAmplitude, re-exported by the
   recorded module Sheaf.Paper.FiniteTorAmplitudeSites, and listed in the record's
   declarations). Both hypotheses are kept, neither strengthened. OK.
7. Ambient RHom_{A_X}(K,M): `(derivedInternalHomOfUniverses.{u+1,u,u} (ProEt.topology X)
   (proEtaleConstantRing X A)).obj (op K, M)`; `derivedInternalHomOfUniverses` is in
   the declarations of def-pur-derived-internal-hom (re-exported publicly by
   DerivedInternalHomMixedUniverses). Universes: site objects u+1, morphisms u, ring
   sheaf in max (u+1) u u = u+1, the same as the intrinsic category of K, M. OK.
8. Conclusion "belongs to D^b_c(X,A)" (bounded, constructible, finite stalks):
   first conjunct `intrinsicFiniteTorsionConstructible l E n hn X (RHom)`: finite
   cohomological support and `IsConstructibleProEtaleModuleSheaf` of every H^i. OK.
9. "bounded constructible étale origin": `∃ L : ProEtale.FiniteCoefficientEtaleDerivedCategory
   X (ULift A)` (an abbrev for `DerivedCategory (Sheaf X.smallEtaleTopology
   (ModuleCat.{u+1} (ULift A)))`, literally the `Etale.DerivedCategoryModule` type of the
   previous accepted module), `Etale.DerivedCategory.isBoundedConstructible` of L, and
   `Nonempty (finiteCoefficientIntrinsicDerivedComparison.obj L ≅ RHom)` with the canonical
   termwise comparison (mapDerivedCategory of the specified intrinsic comparison), not an
   arbitrary functor. The `Finite` instances are passed from the recorded
   `Padic.finite_coefficientExtensionRing` (and its ULift transport); they are derived
   facts, not hypotheses. OK.
10. "k may have characteristic zero and need not be perfect": nothing assumed. OK.

Edge cases: n = 0 is outside the node (hn); n = 1 included; empty X and zero K or M are
covered (no nonemptiness or nonzero hypothesis); char k = 0 and imperfect k admitted;
A = Z/ℓ² type rings: finite-Tor is a hypothesis, not inferred. Single universe u, all
variables bound, autoImplicit false.

Comparison with the previously accepted module (live before f6bf55e2b05, sha256
0650ea19…, PASSed by N1/NT-stage2-cc-5387dc098 on 2026-10-18): the signature is the same
up to (a) `Etale.DerivedCategoryModule (ULift A) X` → the identical abbrev
`ProEtale.FiniteCoefficientEtaleDerivedCategory X (ULift A)`, (b) explicit instance
arguments written with `inferInstance`/named `h :=`, and (c) imports updated to the
current recorded modules (FiniteTorAmplitudeSites, DerivedInternalHomMixedUniverses,
ProEtaleFiniteModuleIntrinsicComparison). Every import exists in the live tree.

Records: the item node differs from live only in `lean` (module, declaration, file,
statement verbatim equal to the file signature, existing false). The six stmt_dep node
files are byte-identical to live. No definition is introduced (H5); the only `sorry` is
the theorem proof (H6). The module and theorem docstrings carry the source place
(Bhatt–Scholze 6.7.13, 6.5.1) and `(blueprint: lem-per-finite-tor-internal-hom-any-field)`,
and the theorem docstring gives the node's eleven proof steps in condensed form (H8). The
statement is not a derived isomorphism, so the 2026-10-21 per-degree rule does not apply.

Searches: Mathlib and lean/Sheaf, lean/WeilConjectures for derived internal Hom
constructibility; the only near match `isBoundedConstructible_finiteTor_derivedHom_by_devissage`
assumes IsSepClosed k with étale endpoints, so not an attachment (as the worker found).

Change made by this reading: only this report section (the original was a self-audit,
H11). No Lean or node change. No compile: no Lean file was changed.

Author's note (original section, kept for the record):


Author's second reading under the dispatcher instruction forbidding other agents;
this is not represented as an independent review. I reopened the node and complete
module and checked the correspondence above against each phrase of the statement.
The first compile exposed missing finite instances in the explicit etale-origin
clause. These were repaired by passing the already recorded finiteness theorem
and its ULift transport as explicit instance arguments; no hypothesis was added.
I checked that both finite-Tor assumptions remain, the RHom expression in the two
conclusion clauses is identical, and the etale-origin witness is bounded constructible.
The recorded dependency interfaces are used unchanged; no dependency repair is included.
The maintainer's independent review remains the mathematical review of this delivery.
