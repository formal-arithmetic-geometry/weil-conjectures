## Worker report

The module Sheaf.AlgebraicGeometry.RegularPrimeDivisorLocalEquations states
AlgebraicGeometry.regularPrimeDivisorLocalEquations, with its sole proof `sorry`.
The node's statement and dependency lists are unchanged. No new definition or dependency
repair is needed. The source read was divisors.tex, lemma-weil-divisor-is-cartier-UFD
(Tag 0AGA), lemma-integral-effective-Cartier-divisor-dvr (0AG9), and
lemma-codim-1-part (0AGB), including the second proof paragraph and final paragraph.

Hypotheses and clauses, individually matched:

- `X D : Scheme.{u}` introduces the ambient scheme and closed subscheme, in any universe u.
- `[IsIntegral X]` gives integrality of X, including nonemptiness.
- `hX : IsRegularScheme X` uses the dependency's definition, which is precisely
  `IsLocallyNoetherian X ∧ IsRegular X`. Thus both regularity and local Noetherianity
  are retained, without a redundant separate instance hypothesis.
- `i : D ⟶ X` and `[IsClosedImmersion i]` give the closed subscheme embedding.
- `[IsIntegral D]` gives the stipulated integral scheme structure on the closed subscheme.
- `ξ : D` and `hξ : IsGenericPoint ξ Set.univ` specify its generic point. Its image
  `i ξ` is the point denoted ξ in the node's ambient local ring.
- `hdim : ringKrullDim (X.presheaf.stalk (i ξ)) = 1` is the stated dimension hypothesis.
- `i.ker.IsInvertible` is the effective Cartier ideal assertion. Despite the name,
  the recorded upstream definition is exactly affine-local generation by a nonzerodivisor,
  not a new module-theoretic definition of invertibility.
- `IsDiscreteValuationRing (X.presheaf.stalk (i ξ))` gives the actual generic ambient
  local ring as a DVR. Its domain instance follows from the supplied integral X.
- `∀ (x : D) (f : X.presheaf.stalk (i x))` includes every divisor point and every
  element of its ambient local ring A. The implication
  `Ideal.span {f} = RingHom.ker (i.stalkMap x).hom → ...` means exactly that f generates
  the defining ideal stalk. For a closed immersion this kernel is the stalk ideal:
  the published Scheme.Hom.ker_stalkMap identifies it with the extension of
  i.ker.ideal U along the germ on any affine neighbourhood. No replacement notion is defined.
- `Prime f` includes f nonzero, f not a unit, and the divisibility alternative for every
  product, exactly as in the parenthesized node description.
- `∃ hp : (Ideal.span {f}).IsPrime` exposes the prime-ideal instance needed to write
  Mathlib's `Localization.AtPrime`. This does not strengthen the result: it is already
  implied by `Prime f` and included to type the dependent localization.
- The ring equivalence e has domain the actual `Localization.AtPrime (Ideal.span {f})`
  and codomain `X.presheaf.stalk (i ξ)`. The condition for every a says that e composed
  with algebraMap equals `X.presheaf.stalkSpecializes ...`, the canonical generization
  homomorphism. The specialization is obtained by applying the continuous i to
  `hξ.specializes (Set.mem_univ x)`. Thus this is the required canonical identification,
  rather than just existence of an unrelated ring isomorphism. Uniqueness of a map out
  of localization follows from the localization universal property; it need not be an
  additional clause.
- The final principal-ideal equality says that the image of this same arbitrary f under
  this same generization map generates the maximal ideal of the generic local ring.
  This is exactly the node's uniformizer definition.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Properties: AlgebraicGeometry.IsIntegral.
- Sheaf.AlgebraicGeometry.IsRegularScheme: AlgebraicGeometry.IsRegularScheme, using
  WeilConjectures.AlgebraicGeometry.Regular: AlgebraicGeometry.IsRegular.
- Mathlib.AlgebraicGeometry.Noetherian: AlgebraicGeometry.IsLocallyNoetherian.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: AlgebraicGeometry.IsClosedImmersion.
- Mathlib.AlgebraicGeometry.IdealSheaf.Basic: AlgebraicGeometry.Scheme.Hom.ker and
  Scheme.Hom.ker_apply; the former is the recorded defining ideal sheaf.
- WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible:
  AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.
- Mathlib.RingTheory.KrullDimension.Basic: ringKrullDim.
- Mathlib.RingTheory.Localization.AtPrime.Basic: Localization.AtPrime.
- Mathlib.RingTheory.DiscreteValuationRing.Basic: IsDiscreteValuationRing and
  IsDiscreteValuationRing.irreducible_iff_uniformizer.
- Mathlib.Topology.Sober: IsGenericPoint and IsGenericPoint.specializes.
- Mathlib.AlgebraicGeometry.FunctionField supplies domain instances for integral-scheme
  stalks, needed by the DVR conclusion.

All recorded proof-dependency modules are imported as ordinary imports when not already
publicly imported for the statement: Mathlib.AlgebraicGeometry.AffineScheme (the affine
stalk localization signatures), Mathlib.AlgebraicGeometry.Modules.Tilde (tilde.toStalk
and its IsLocalizedModule instance), Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
(the closed subscheme construction), Mathlib.RingTheory.Ideal.UFD
(UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one),
Mathlib.RingTheory.Noetherian.Defs (IsNoetherianRing),
WeilConjectures.RingTheory.IsRegularSystemOfParameters
(IsLocalRing.IsRegularSystemOfParameters),
Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization
(regularLocalUFDBoundaryFactorization), and
WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
(IsRegularLocalRing.isDiscreteValuationRing).
The theorem docstring contains all eight proof steps of the node, including finite
denominator clearing and the arbitrary-generator argument.

Edge cases checked before writing: integral schemes are nonempty, so there is no empty-D
exception. D = X and a zero-dimensional ambient generic stalk cannot satisfy hdim = 1.
For x = ξ, the specialization is reflexive and the localization comparison is the usual
local-ring identification. A zero or unit f cannot generate this nonzero proper prime;
Prime f retains both exclusions. For a DVR and its reduced closed point the statement
says that every generator of the maximal ideal is prime and is a uniformizer. For a
regular surface and an integral codimension-one curve it uses stalk generators even
at singular points of the curve; no regularity of D is assumed. The Cartier condition
also covers points outside D, where the ideal has equation 1. No global Noetherianity,
finite-dimensionality, characteristic restriction, or noncanonical map is introduced.

Searches actually run with msearch.py (NP, this item):

- leanfinder: “An integral closed subscheme of codimension one in a regular locally
  Noetherian scheme is an effective Cartier divisor with generic discrete valuation ring”.
  Eight hits concerning integral schemes, fields and domain stalks; no exact result.
- loogle: `"AlgebraicGeometry", "Cartier"`. Zero hits.
- grep in Mathlib/AlgebraicGeometry: `Cartier|prime.divisor|locally.?factorial`.
  Zero hits according to the wrapper.
- leansearch: “An integral codimension one closed subscheme of a regular locally
  Noetherian scheme is an effective Cartier divisor”. Eight hits concerning subscheme,
  integral morphisms, immersions and integral/reduced schemes; no exact result.
- rg in lean/WeilConjectures and lean/Sheaf:
  `regular.*[Pp]rime[Dd]ivisor|prime[Dd]ivisor|lem-per-regular-prime-divisor-local-equations|Cartier.*[Rr]egular|[Rr]egular.*Cartier`.
  Related modules include RegularCartierGenericStalkDvr, which requires the effective
  Cartier assumption already and gives only the DVR clause, and SmoothCodimensionOneCartier,
  which assumes smoothness and states a different result. Neither states this node.
  The only hit for this node id is a proof-docstring citation in SymmetricAbelImageGeometry.
- rg in dag/lean_names_upstream.json for this node id: no match.

No statement fault or dispute was found. The named module compiled through scompile.py
both in its sandbox name and its intended library name, with no errors or unexpected
warnings. The only postponed proof is regularPrimeDivisorLocalEquations.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
