## Worker report

The module `Sheaf.RingTheory.IsN1OfLocalCharacterization` states
`isN1_of_local_characterization`, with its sole proof `by sorry`.
The docstring follows all eight proof steps of the node and names their dependencies.
No definitions, new nodes, dependency modules, or statement corrections are needed.

Source checked: [Stacks Project, Algebra, Lemma 10.161.15, Tag 0333](https://stacks.math.columbia.edu/tag/0333),
implication (1)+(2) => N-1. The literature checkout is absent on this machine, so the
published tag was opened directly. Its hypotheses and conclusion agree with this node.

Each hypothesis and clause is represented as follows:

- The commutative integral domain A is `(A : Type u) [CommRing A] [IsDomain A]`.
- Noetherian is `[IsNoetherianRing A]`, exactly every ideal finitely generated.
- The fraction field K is `(K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]`.
  Both universes are explicitly bound and independent.
- Some nonzero f is `hAway : ∃ f : A, f ≠ 0 ∧ ...`. No f is fixed or assumed a unit.
- Its principal localization is `Localization.Away f`.
- Normality of that ring is exactly the recorded normal-ring match:
  `∀ (p : Ideal (Localization.Away f)) [p.IsPrime],
  IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`.
  This uses the normal-ring clause, without replacing it by a new predicate or assuming
  A itself normal.
- Every maximal ideal is quantified by `∀ (m : Ideal A) [m.IsMaximal], ...`.
- The local ring A_m is `Localization.AtPrime m`; maximality supplies primality.
- The N-1 local hypothesis is
  `IsN1 (Localization.AtPrime m) (FractionRing (Localization.AtPrime m))`.
  N-1 is intrinsic to a domain; this chooses its canonical fraction field. That field
  is canonically isomorphic over A_m to K, since A_m is a localization of the domain A
  away from zero. Thus this is the node's local condition, not an additional choice
  of an algebra map on K. Both the canonical fraction field and its algebra and
  fraction-ring instances elaborate without auxiliary assumptions.
- The conclusion is `IsN1 A K`. By the existing definition this is literally
  `Module.Finite A (integralClosure A K)`, giving both the finite-integral-closure clause
  and the equivalent N-1 formulation. No extra conclusion is included.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (docstring and abbreviation).
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, with
  `IsDomain` and `Mathlib.RingTheory.Localization.AtPrime.Basic`'s `Localization.AtPrime`,
  as prescribed by `def-weil-pbc-normal-ring.mathlib_match`. No dependency module is
  required: that record explicitly prescribes the inline prime-localization predicate.
- `Sheaf.RingTheory.JapaneseDomain`: `IsN1` (full signature, body and docstring read).
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`, through `IsN1`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, through `IsN1`.

Auxiliary existing notation: `Localization.Away` is localization at the powers of f;
`Localization.AtPrime` is localization at the prime complement. `FractionRing` is the
canonical fraction field. There are no private copies of these notions. All imports
are used either directly in the signature or by the chosen N-1 definition.

Edge cases checked before writing:

- A field is included, with its zero maximal ideal, and any nonzero f works.
- Taking f = 1 is allowed; f = 0 is expressly excluded.
- The zero ring is excluded by the node's integral-domain premise, not by a new premise.
- There is no restriction on characteristic, dimension, or number of maximal ideals.
- Normality is quantified over all prime ideals, and both clauses (domain and integral
  closedness) are present. The maximal quantifier is not restricted to nonzero ideals.
- The canonical local fraction field lives in the universe of A; this involves no
  quantification over undersized test fields and cannot make the hypothesis vacuous.

Searches (2026-10-11):

- `msearch.py ... leanfinder`, query: "A Noetherian domain has finite normalization if
  its maximal localizations have finite normalization and some nonzero principal
  localization is normal". Eight hits, including
  `AlgebraicGeometry.isNoetherianRing_of_away`, `IsNoetherianRing.of_isLocalization_maximal`,
  `isDedekindRing_iff`, and `integralClosure.isNoetherianRing`; none states this criterion.
- `msearch.py ... loogle`, query: `IsIntegrallyClosed, IsNoetherianRing`.
  Six hits: DVR TFAE results and finite/noetherian integral closure for finite separable
  extensions of an already integrally closed base. None matches this local N-1 criterion.
- `msearch.py ... grep`, query: `IsN1|Japanese|finite.*integralClosure`, subdirectory
  `RingTheory`. Six hits in Zariski's main theorem, localization of integral closures,
  and different ideals; none states this lemma.
- `rg` of `N1|N-1|normal.*local|local.*normal` in project `lean/Sheaf/RingTheory`
  and source `WeilConjectures/RingTheory`: existing `IsN1`, localization preservation,
  and analytically-unramified N-1 criteria found, but no identical statement.
- `rg` of the item id in source `WeilConjectures`: no hit.
- `rg` of `isN1_of_local_characterization|finite.*normalization|N-1|Japanese` in
  source `WeilConjectures`: only unrelated geometric and Noether-normalization text.
  The proposed declaration name has no source or Mathlib collision.

Server single-file compilation succeeded with exit code 0 and no warnings.
No statement dispute or node fault was found.

## Second reading by K1

I reread the item statement, its five statement dependencies, and Stacks Project Algebra
Lemma 10.161.15 (Tag 0333), implication (1)+(2) => N-1. The source states: (i) a
Noetherian integral domain R; (ii) existence of a nonzero f whose principal localization
R_f is normal; (iii) every maximal localization R_m is N-1; and (iv) the conclusion that
R is N-1, equivalently that its integral closure in the fraction field is finite as an
R-module. The Lean renders these as follows.

- The ring is `(A : Type u)` with `[CommRing A] [IsDomain A]`.
- Noetherianity is `[IsNoetherianRing A]`, Mathlib's every-ideal-finitely-generated
  predicate.
- The fraction field is `(K : Type v)` with `[Field K] [Algebra A K]
  [IsFractionRing A K]`; both universes are explicit and no characteristic is fixed.
- The principal-open hypothesis is `hAway : ∃ f : A, f ≠ 0 ∧ ...`, so f is nonzero and
  is not assumed to be a unit. Its localization is exactly `Localization.Away f`.
- Normality of `A_f` is rendered by
  `∀ (p : Ideal (Localization.Away f)) [p.IsPrime],
  IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`,
  which is the recorded normal-ring definition (normal domain at every prime).
- The local condition is
  `∀ (m : Ideal A) [m.IsMaximal], IsN1 (Localization.AtPrime m)
  (FractionRing (Localization.AtPrime m))`; this is N-1 for each local ring using its
  canonical fraction field, the intrinsic fraction field of that localization.
- The conclusion is `IsN1 A K`, whose existing definition is exactly
  `Module.Finite A (integralClosure A K)`, i.e. finite normalization in K.

No hypothesis, object, quantifier, or conclusion clause is added, dropped, strengthened,
or weakened. The source's zero-ring exclusion is supplied by `[IsDomain A]`; there is no
extra Noetherian, characteristic, separability, dimension, or finiteness assumption.
Edge cases checked: fields (including the zero maximal ideal), f = 1, arbitrary
characteristic, any number of maximal ideals, and all prime ideals in the normality
quantifier. The zero ring is excluded only because the source says integral domain. The
canonical local fraction fields introduce no smaller test universe.

I searched Mathlib and the source project by LeanFinder, Loogle, grep, and `rg` for N-1,
Japanese domains, finite integral closures, and local normality; no identical declaration
was found. I also checked the dependency declarations: `IsNoetherianRing` (Mathlib), the
inline normal-ring conjunction using `IsIntegrallyClosed` and `Localization.AtPrime`,
`IsN1` from `Sheaf.RingTheory.JapaneseDomain`, Mathlib's `integralClosure`, and
`Module.Finite`. The module uses these declarations directly and introduces no private
copies. The Stacks tag page and source text were checked directly.

There were no mismatches to repair. The existing worker module and node `lean` record were
left unchanged. Compilation with `scompile.py` succeeded with exit code 0 and no warnings.
