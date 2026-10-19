## Worker report

The module `Sheaf.AlgebraicGeometry.KummerRootRegularDivisorPurity` states
`AlgebraicGeometry.Etale.kummer_root_regular_divisor_purity`. Its only theorem has
proof `sorry`. Six data helpers name the actual AdjoinRoot algebra, its spectrum,
root coordinate, constants-induced projection, quotient divisor and quotient-induced
inclusion. None chooses algebraic data or maps from an existence theorem.

Source read: ILO XVI Proposition 3.4.5 and Lemmas 3.4.6--3.4.9, printed pp.246--248
(PDF pages 252--254), including the relative functor and first-nonzero-cohomology argument.
The module docstring records all eight DAG proof steps. No statement correction is needed.

Hypothesis and clause correspondence:

- Prime ell: `(ℓ : ℕ) (hℓ : ℓ.Prime)`. Coefficients are the published
  `regularClassCoefficients ℓ 1 = ULift (ZMod (ℓ ^ 1))`, canonically F_ell.
  The lift is to the existing small-etale coefficient universe u+1, with no relation
  imposed between independently varying universes.
- Ordinary small-etale derived categories and finite Tate twists: the published
  `punctualPurityClassMap` uses D+ of `Sheaf X.smallEtaleTopology (ModuleCat A)`.
  Its fully faithful inclusion in D reflects isomorphisms. Its target is the closed
  right adjoint applied to the finite Tate sheaf in degree one, shifted by two.
  Thus its IsIso is exactly the displayed A_D -> i^! A_X(1)[2] test, with the
  positive supported Kummer normalization from the recorded class-calculus dependency.
- The introductory punctual-purity definitions are already `IsPunctuallyPureAt` and
  `IsPunctuallyPure` in `Sheaf.AlgebraicGeometry.PunctualPurity`; this landed definition
  node is added to stmt_deps and imported, without copying it. The former explicitly
  uses the dimension of the local stalk, the residue map and its closed-point spectrum.
  Punctual purity is terminology here, and is not assumed in the theorem.
- X=Spec B: `B : CommRingCat.{u}` and literal `Spec B`. Noetherianity is
  `[IsNoetherianRing B]`, equivalent to Noetherianity of its affine spectrum.
  Regularity is `hB : IsRegularScheme (Spec B)`, the recorded predicate including
  local Noetherianity and stalkwise regularity. Invertibility is `hInv : IsUnit (ℓ : B)`.
- The nonzerodivisor equation is `(f : B) (hf : IsSMulRegular B f)`, injectivity of
  multiplication by f, without assuming that f is a nonunit.
- D=Spec B/(f) and its regularity are precisely `hD : IsRegularScheme
  (Spec (.of (B ⧸ Ideal.span {f})))`. Its inclusion is literally Spec of the quotient map.
- X'=Spec B[U]/(U^ell-f) is `divisorRootScheme`, using
  `AdjoinRoot ((Polynomial.X : Polynomial B)^ℓ - Polynomial.C f)`. D'=V(U) is
  `divisorRootDivisor`, the quotient by the span of `AdjoinRoot.root`.
- X' regular and D' regular are the first two `IsRegularScheme` conjuncts. The
  quotient coordinate is explicitly a nonzerodivisor (`IsSMulRegular` conjunct).
  The kernel ideal sheaf of its closed inclusion is invertible (`.ker.IsInvertible`),
  expressing the effective Cartier divisor, including empty support.
- D' is isomorphic to D: `∃ e : divisorRootDivisor ... ≅ Spec (.of (B ⧸ ...)), ...`.
  The structural-map equation makes this the natural isomorphism over X; since i is
  a monomorphism it cannot select an unrelated abstract isomorphism.
- The purity equivalence is exactly the iff of the two `IsIso
  (punctualPurityClassMap ... 1 ...)` expressions. The existential Noetherian,
  closed-immersion, stalk-regular-immersion and global invertibility witnesses are
  geometric consequences of the hypotheses, included in the conclusion to evaluate
  this existing dependent interface. They add no hypothesis and are proof-irrelevant.
- Finite local freeness of rank ell is the upstream
  `(divisorRootProjection ...).IsFiniteLocallyFreeOfDegree ℓ`. This includes finiteness,
  flatness, local finite presentation and fibre degree at every point. It is not merely
  module finiteness or an unranked finiteness assertion.
- Surjectivity of p is `Surjective (divisorRootProjection ...)`.
- The last three conjuncts identify the inverse image of D(f) with D(U) and assert
  `Surjective` and `Etale` for the actual `morphismRestrict p (PrimeSpectrum.basicOpen f)`.
  Thus the map is precisely the canonical map on both divisor complements.

Dependency declarations used, with their recorded sources opened:

- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`;
  upstream `WeilConjectures.AlgebraicGeometry.Regular`: `IsRegular`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` (read with scompile --source):
  `Etale.DerivedCategoryModule`, D+, D, cohomology and torsion interface. The category
  in the class map is this same coefficient-sheaf encoding.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`:
  `Scheme.finiteEtaleTateTwist`, used by the class calculus's signed finite Tate sheaf.
- `Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus`:
  `RegularImmersionClassFamily`, `regular_immersion_class_calculus`,
  `regularClassCoefficients`, `regularClassTwist`.
- `Sheaf.AlgebraicGeometry.PunctualPurity`: `regularImmersionClasses`,
  `punctualPurityClassMap`, `IsPunctuallyPureAt`, `IsPunctuallyPure`. Reuses its
  `supportedExtPlusHom` and canonical closed derived adjunction; no new class or
  exceptional functor is introduced.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.residue`, `Scheme.Hom.residueFieldMap`; the local-ring and residue-field
  operations of the reused punctual-purity definitions.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`, used by punctual purity.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion` and the
  quotient-map instance; `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`, X and C.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.IsFiniteLocallyFree`, `Scheme.Hom.IsFiniteLocallyFreeOfDegree`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.RingTheory.AdjoinRoot`: `AdjoinRoot`, `AdjoinRoot.root`, its algebra map;
  `Mathlib.AlgebraicGeometry.Restrict`: `morphismRestrict`.

Every currently stated proof dependency is imported without public visibility.
The three proof-only nodes `lem-per-divisor-purity-strict-local-criterion`,
`lem-per-kummer-classifying-purity-criterion`, and `lem-per-kummer-relative-cone-functor`
have no recorded Lean declaration at inspection, so have no import to add. They are
named in the proof docstring. No missing statement notion required a new node.

Edge cases checked before writing: ell=0 and ell=1 are excluded exactly by primality;
ell=2 is included; no characteristic restriction beyond ell invertible. The zero ring
and empty spectrum are allowed. Unit f gives empty D and D', with the zero-category
purity test and an etale cover on the whole ambient scheme. Nonunit f has positive
codimension on its support. No connectedness, excellence, domain, local-ring,
strict-henselian, finite-dimensional-scheme or nonempty-divisor assumption is added.

Searches (2026-10-19):

- msearch LeanFinder, `Regular divisor purity is invariant under adjoining an ell-th
  root of a regular parameter`: eight unrelated algebra hits, including
  `AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero`; no purity theorem.
- msearch Loogle, `AdjoinRoot, IsRegularRing`: zero hits.
- msearch LeanSearch, `Cohomological purity of a regular divisor is invariant under
  adjoining a prime-th root of its equation`: eight adjoin-root/cyclotomic hits;
  none states the purity equivalence.
- msearch grep, `Kummer.*purity|kummer.*purity|regular.*divisor` under AlgebraicGeometry:
  zero hits. Direct rg of Mathlib AlgebraicGeometry for purity/Kummer also gave no match.
- rg of WeilConjectures and lean/Sheaf for the item ID and root-purity names found no
  statement match. Broader class/punctual-purity searches found the published
  PunctualPurity interface, which this delivery uses. Root-algebra/divisor searches
  found other covers (notably global-section Kummer torsors), not this actual affine
  quotient divisor and its purity equivalence.

Validation: scompile.py compiled the file in sandbox and library contexts, 6.7 and
6.8 seconds, with no errors or warnings. No proof is supplied. The underlying
class-calculus theorem records a pre-existing disputed uniqueness proof obligation;
this delivery uses that published canonical-family interface and does not change it.

## Second reading by Q65

Self-check, not an independent-agent review: the dispatcher explicitly forbids starting
other agents and the maintainer provides the independent reading. Reopened the item,
module and dependency declarations and checked every binder and conjunct above.
In particular, the theorem never assumes punctual purity; the D+ map is the published
transpose, not the supported Ext morphism tested for invertibility; ell is the cover
rank as well as the coefficient prime; D' has the quotient scheme structure; and the
complement map is fixed by morphismRestrict. The conclusion supplies all dependent
geometric witnesses rather than imposing them as hypotheses. The over-X equation for
the divisor isomorphism excludes an unrelated isomorphism. No mismatch was found.
