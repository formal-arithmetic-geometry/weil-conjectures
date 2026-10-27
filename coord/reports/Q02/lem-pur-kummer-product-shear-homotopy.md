## Worker report

The module `Sheaf.Paper.KummerProductShearHomotopy` states
`WeilConjectures.PurityFiniteSetting.kummerProduct_shear_homotopy` with `sorry`.
It constructs only helpers belonging to this statement. No theorem is proved and
no definition has postponed data. The natural-language statement is unchanged.
There is no repair note for this item in `coord/repair-notes`.

Clause-by-clause correspondence:

- Finite datum k, ell, E, positive n and A: `P : PurityFiniteSetting.{u}`. Its
  existing fields include `level_pos : 1 ≤ level` and the prescribed coefficient
  field datum. The coefficient ring is `P.Coefficient`, the standard size lift of
  the quotient. There is no ramification divisibility assumption.
- Any k-scheme: `X : Scheme.{u}` and `aX : X ⟶ Spec (.of P.field.k)`, with no
  smoothness, regularity, finite type or separation assumption.
- Ordered c-tuple: `c : ℕ`, `h : Fin c → Γ(X, ⊤)`. Its closed subscheme and
  immersion are the existing `X.zeroLocusSubscheme (Set.range h)` and
  `X.zeroLocusSubschemeι (Set.range h)`. These are ideal-defined schemes, not
  reduced closed subsets.
- The concrete K_X(h) formula is exactly the existing
  `P.frameBoundaryProduct X aX c h`. Reading its definitions shows that each
  factor is `frameBoundary` of the specified function, formed from `frameKummer`
  on `X.basicOpen f` using `X.basicOpenUnit f`. Its boundary is the Yoneda
  realization of the support localization boundary. `frameCupNext` uses the
  published `supportedCup`, the intersection identification and twist tensor
  multiplication. `frameFold` appends the last factor to the prefix, so the
  product is left-associated and retains the order. Its type is
  `cupSupportedHom P (X.zeroLocusSubschemeι (Set.range h))
  ((cupSingle P X).obj (P.frameTwist X c)) (2 * (c : ℤ))`.
- The case c=0 is already defined: `frameBoundaryProduct` reduces to
  `frameEmptyClass`, the inverse constant-coefficient restriction followed by
  the zero-shift comparison. The empty ideal defines full support. This
  construction is reused, not restated or restricted to c≥2; only the shear
  assertion has the node's `_hc : 2 ≤ c`.
- Distinct indices and scalar: `i j : Fin c`, `_hij : i ≠ j`, `a : Γ(X, ⊤)`.
  The scalar need not be a unit. `kummerShearTuple` changes precisely entry i.
- T, p, t, s0 and s1: Mathlib's
  `AffineSpace (ULift.{u} (Fin 1)) X`, its canonical projection `↘ X`,
  `AffineSpace.coord X (ULift.up (0 : Fin 1))`, and the existing
  `AffineSpace.zeroSection` and `AffineSpace.oneSection`.
- H: `kummerShearHomotopyTuple` applies the shear to the projection pullbacks,
  with scalar `t * p.appTop a`. Thus entry i is
  `p.appTop (h i) + (t * p.appTop a) * p.appTop (h j)` and every other entry is
  `p.appTop (h b)`. Associativity is the displayed formula in the node.
- C_h'=C_h as closed subschemes: the existential `e` and its equation `he`
  provide an isomorphism over X. This is equality of closed subobjects, not
  literal equality of arbitrary chosen scheme presentations. Its map is unique
  because the closed immersion is monic.
- C_H=T times_X C_h as closed subschemes: existential `eT` and its equation
  identify the H zero subscheme with `pullback C_hι p`, over T using
  `pullback.snd`. This includes nonreduced scheme structures.
- Eta is the real definition `kummerShearHomotopyClass`: exactly
  `frameBoundaryProduct T (p ≫ aX) c H`, not a class selected by existence.
  It initially has support C_H, identified with the displayed fibre product by
  eT. Thus it is the requested element of degree 2c and twist c.
- The inverse-image supports for s0 and s1 are specified by existential g0,g1
  and `sq0`, `sq1 : ChosenCartesianSquare ...`. These are conclusions, not
  additional assumptions. Their equations and pullback isomorphisms express
  exactly the inverse-image support condition, using C_h at both endpoints.
- All coefficient and pullback identifications are canonical:
  `kummerTuplePullback` calls the existing `functorialCupPullback true` on the
  actual representative. This applies exact inverse image, the uniquely
  restriction-normalized closed coefficient exchange and the root-normalized
  Tate twist comparison. It introduces no arbitrary map.
- s0*eta=K_X(h): first equality in the endpoint conjunction.
- s1*eta=K_X(h'): second equality, where `kummerShearedProduct` reads the
  existing product on C_h using exactly `frameClosedCoefficientIso e he`.
- s0*eta=s1*eta: third equality, both in the original supported Hom group.
- Consequently K_X(h')=K_X(h): last equality of that conjunction. The frame
  neighbourhood assertion is the specialization to its ambient k-scheme;
  there is no assertion or assumption that T is an etale frame neighbourhood.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, `Coefficient`,
  `constant`, `twist`; this is the same fixed field/finite extension/level datum.
- `Sheaf.Paper.PurityFrameClass`: `frameBoundaryProduct`, `frameEmptyClass`,
  `frameCupNext`, `frameClosedCoefficientIso`, and the main `frameClass`.
  The main declaration has frame hypotheses, but its existing public
  `frameBoundaryProduct` is already defined on arbitrary tuples, so no
  dependency repair is needed.
- Its owners `PurityFrameKummer` and `PurityFramePrincipalBoundary`:
  `frameTwist`, `frameKummer`, `frameBoundary`; the latter uses the exact
  coefficient extension and concrete Kummer extension, not an unspecified class.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the recorded owner of
  `def-coefficient-twists-detailed`, read with its reexported
  `FixedFinitePositiveCoefficientTwist` interface (`diagonalExponent`,
  `diagonalExponent_annihilates`). The finite positive twists used by
  `frameTwist` are precisely its finite root-tensor presentation, not the Qbar
  twisting functor which is merely the node's main recorded declaration.
- `Sheaf.Paper.SupportedCup`: `cupSupportedHom`, `cupSingle`, `supportedCup`;
  the existing frame product uses the exact supported cup construction.
- `Sheaf.AlgebraicGeometry.SupportCohomology`:
  `ProEtale.supportSections`, `supportCohomology`, `supportHypercohomology`.
  The support Hom representative is the published model used by the concrete
  frame class and supported cup; it is not a new cohomology definition.
- `Sheaf.AlgebraicGeometry.SupportLongExact`: `exists_support_longExact`,
  including its pro-etale finite-coefficient clause. Imported for the proof.
- Mathlib `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`, `over`,
  `coord`, `homOfVector`; the zero/unit sections are its published extensions.
- `Sheaf.Paper.SupportedCupFunctoriality`: `functorialCupPullback`,
  `functorialCupExchange`, and `functorialCupTwistPullback`, owned by the
  already-landed definition node `def-pur-supported-class-operations`
  (`existing: true`). This definition node is cited in `stmt_deps` for the
  canonical pullback interface used through `kummerTuplePullback`.
  The theorem `supportedCupFunctoriality` belongs to
  `lem-pur-supported-cup-functoriality`, retained in `proof_deps`.
  There are no other node-field changes besides `lean`.
- Proof import `Sheaf.Paper.PurTwistSheafLocallyFree`:
  `Scheme.pur_twist_sheaf_locally_free`, as specified by the DAG proof.
  The existing `supportedAffineLineHomotopy` interface was read for the
  proof plan, but its module `Sheaf.Paper.SupportedAffineLineHomotopy` is
  omitted: the server preflight identifies it as an import of a route-pivot
  dropped node (`def-per-canonical-etale-supported-pullback`), prohibited by
  `coord/route-pivot-dropped.txt`. The statement uses no declaration from
  that module; its canonical pullbacks are from SupportedCupFunctoriality.

Edge cases checked before writing:

- c=0: the reused construction is the unit on the full zero-ideal subscheme;
  the shear theorem correctly requires c≥2. At c=1 no distinct pair exists.
- a=0: H is the constant tuple and h'=h.
- h_j a unit: the total closed support is empty; support transports and cups
  still make sense. No nonemptiness or nonvanishing hypothesis is imposed.
- All functions zero: full closed support, with every complementary open empty;
  the Kummer/boundary constructions remain defined.
- Nilpotents and nonreduced X: (h_i+a*h_j)-a*h_j=h_i is an ideal identity,
  not just an equality of radicals. Empty X and disconnected X are allowed.
- The least finite coefficient level n=1 and ramified levels not divisible by
  e remain included. The affine line has no additional frame condition.
- Universes: schemes use arbitrary u, the small-site module coefficients use
  the published lift to u+1, and the affine coordinate index is `ULift (Fin 1)`.

Searches performed (no exact existing theorem):

- msearch LeanFinder: "Elementary shear invariance of the ordered supported
  Kummer boundary cup product by affine line interpolation". Eight returned
  hits concern cube boundaries, box integrals, Noebeling maps, simplicial
  boundaries, root strings and a representation bar complex; none concern
  supported Kummer cohomology or this interpolation.
- msearch Loogle: `AlgebraicGeometry.Etale, "kummer"`: zero hits.
- msearch LeanSearch: "The supported Kummer cup product is unchanged when one
  function is replaced by itself plus a multiple of another". Eight hits
  concern alternating maps, cusp forms, Kaehler differentials, group
  cohomology functoriality and meromorphic divisors; none match.
- msearch grep: `kummer.*(shear|homotopy)|[Bb]oundaryProduct.*shear`: zero hits.
- rg in both `lean/WeilConjectures` and `lean/Sheaf`, using the item id,
  `kummer.*shear`, `[Bb]oundaryProduct.*shear`, and the proposed declaration
  names: no duplicate declaration. Broader searches found the existing
  `frameBoundaryProduct`, `SupportedAffineLineHomotopy` and upstream
  `KummerProductBaseChange` / `RegularImmersionProduct`; the latter are
  etale coefficient and base-change/product results, not the present
  arbitrary finite-coefficient pro-etale shear assertion. Reused all existing
  constructions instead of duplicating them. The upstream name index was
  searched for every new full-name component with no hit.

The source paragraph and the node's complete five-step proof were read. No
statement correction, missing notion, disputed assertion or dependency module
is needed. All new helper definitions are listed in lean.declarations and carry
source/blueprint docstrings. The sole postponed theorem has the matching DAG
statement and the complete five-step proof in its docstring.

Validation: prescribed scompile.py compiled the single delivered file in both
sandbox and library modes, cleanly (21.0 s and 23.9 s respectively,
after the import repair), with no
errors or extra warnings. Automatic implicits are disabled; all universes and
binders are explicit. Every line is at most 100 columns.

Dry-run repair: removed the route-pivot-prohibited homotopy module import
after the server preflight rejected it. No statement or construction changed.

## Returned-delivery repair

Repaired H2 from the independent review of immutable head `f914c635e976`:
replaced the added theorem-node statement dependency
`lem-pur-supported-cup-functoriality` with its definition owner
`def-pur-supported-class-operations`. The owner record explicitly lists
`functorialCupPullback` and is `existing: true` on
`Sheaf.Paper.SupportedCupFunctoriality`. Read that record and the actual
pullback, exchange, and twist-pullback signatures and docstrings. The
functoriality theorem remains a proof dependency. Updated the dependency
explanation above; the Lean file is byte-for-byte unchanged from the saved
returned packet. No mathematical statement or proof plan changed.

Repair validation: `scompile.py` compiled the unchanged delivered module
cleanly in sandbox mode (15.6 s) and library mode (15.5 s). Self-check confirms
the recorded signature is verbatim, the JSON layout is preserved, and the only
non-`lean` difference from the current read clone is the authorized definition
owner added to `stmt_deps`; `proof_deps` is unchanged.

## Second reading by Q02

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
