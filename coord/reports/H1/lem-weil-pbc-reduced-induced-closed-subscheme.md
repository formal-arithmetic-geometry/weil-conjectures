## Worker report

Module: `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`; declaration:
`AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`.
The only proof is `sorry`. No definitions, new nodes, or dependency replacements are needed.
No statement correction or statement dispute.

Source checked: https://stacks.math.columbia.edu/tag/01J3, Lemma 26.12.4 and its entire proof,
and its following definition (01J4). The repository does not contain the cited
`literature/stacks-project/schemes.tex`, so the official Stacks page was read instead.

Hypotheses and clauses:

- A scheme X: `(X : Scheme.{u})`, with the universe explicitly bound. A closed subset T:
  `(T : TopologicalSpace.Closeds X)`. No finiteness, separation, or reducedness of X is assumed.
- The specified ideal on EVERY open U: the first conjunct asserts
  `f ∈ (vanishingIdeal T).idealOfOpens U ↔ ∀ t ht, t ∈ T → X.evaluation U t ht f = 0`.
  `evaluation` is germ followed by the residue map to `X.residueField t`, so it is exactly
  the residue-field vanishing condition, including the intersection with U.
- Clause (1), sheaf of ideals and quasi-coherence: `vanishingIdeal T : X.IdealSheafData`
  uses the dependency's agreed encoding of quasi-coherent ideal sheaves, not a private
  predicate. `idealOfOpens` is its sheaf of ideals on arbitrary opens, realized as the kernel
  of the map to the structure sheaf of the subscheme. Its corresponding module sheaf is
  the existing `toModules` in the imported Module file. This follows the same representation
  convention as `def-sbc-closed-immersion-ideal-sheaf`.
- Clause (1), affine uniqueness: `∀ U : X.affineOpens, ∃! I : Ideal Γ(X,U), I.IsRadical ∧
  PrimeSpectrum.zeroLocus I = U.2.fromSpec ⁻¹' T`. The next conjunct identifies the affine
  ideal with `PrimeSpectrum.vanishingIdeal` of exactly that set. This is the unique radical
  ideal in the preceding conjunct, since the vanishing ideal of a zero locus is its radical.
- Clause (1), equality with the associated ideal sheaf on U: rendered in the existing
  `IdealSheafData` encoding. The explicit basic-open conjunct says the ideal on D(g) is
  the extension of the affine ideal along the restriction map, i.e. I_g. These are the
  sections of the associated ideal sheaf on the basis D(g), compatibly with restriction;
  equality of subsheaves on a basis is precisely the claimed equality with tilde I.
  This compatibility is also a field of `IdealSheafData`; repeating it makes the local
  description visible without defining another tilde or ideal sheaf.
- Clause (2), cut out by the ideal: use the existing `(vanishingIdeal T).subschemeι`;
  the `IsClosedImmersion` conjunct and the kernel equality state that it is the closed
  immersion with that ideal. `IsReduced` and `Set.range ... = T` give the two specified
  properties. The `IsPullback` conjunct identifies its inverse image over each affine open
  with the quotient spectrum, with bottom map `U.2.fromSpec` and right arrow the subscheme
  inclusion. The top-left object of the square is definitionally
  `Spec (.of (Γ(X,U) ⧸ (vanishingIdeal T).ideal U))`, as defined by `subschemeCover`.
  Thus the square identifies the actual morphism with the quotient map, not merely its
  source ring or an unconnected abstract isomorphism.
- Clause (3): quantify every `Z' : Scheme.{u}` and `i' : Z' ⟶ X` with exactly
  `[IsClosedImmersion i'] [IsReduced Z']` and the range equality. The conclusion is
  `i'.ker = vanishingIdeal T` and `∃! φ : Z' ≅ ...subscheme, φ.hom ≫ ...subschemeι = i'`.
  Composition is in Lean's left-to-right categorical order. The unique object quantified
  is an isomorphism, as the node requires.
- The final sentence names this closed subscheme; the module docstring and declaration
  docstring use that name for Mathlib's existing construction, with no duplicate definition.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`,
  `Spec.map` (scheme, morphisms, spectrum, quotient spectrum morphism).
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.Hom.residueFieldMap`
  (the latter was read as part of the dependency; no morphism of residue fields is needed
  here), `Scheme.evaluation` for sections vanishing in residue fields.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.Hom.ker`,
  `Scheme.IdealSheafData`, `Scheme.IdealSheafData.vanishingIdeal`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`: existing `idealOfOpens`
  (its full definition and `toModules`/`toModulesι` and their section descriptions were read).
  Its import supplies the existing subscheme construction and the other basic scheme imports.
  The explicit Mathlib ResidueField and ClosedImmersion imports supply the evaluation and
  closed immersion declarations used in the statement.

Edge cases checked mathematically before writing: empty scheme; T empty (unit ideal,
empty quotient spectrum); T all of X (nilradical ideal and reduction, not X itself unless
X is reduced); nonreduced X; arbitrary nonaffine U; zero section and empty U (vacuous
pointwise condition agrees with the ideal); zero ring on an empty affine open. No
nonemptiness or domain hypotheses exclude any of these. All scheme and ring constructions
use the same arbitrary explicitly declared universe u. No independent test universe occurs.

Searches (2026-10-11):

- msearch.py leanfinder: `reduced induced closed subscheme vanishing ideal unique isomorphism`:
  8 hits, including affine_isReduced_iff, vanishingIdeal_top, and nilradical_eq_bot;
  none states the full node.
- msearch.py loogle: `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal,
  AlgebraicGeometry.IsReduced`: 0 hits.
- msearch.py grep: `reducedInduced|reduced induced|vanishingIdeal`, restricted to
  AlgebraicGeometry/IdealSheaf: 11 hits, including vanishingIdeal and map_vanishingIdeal;
  definitions and partial properties, no full statement.
- rg in WeilConjectures for vanishingIdeal/reduced induced found
  `isReduced_subscheme_vanishingIdeal` and `ker_eq_vanishingIdeal`; their full signatures
  and docstrings were read. They establish separate pieces, not all the node's clauses.
- rg for the item id in WeilConjectures: no match. rg for
  `reduced_induced_closed_subscheme` in Mathlib, WeilConjectures, and lean/Sheaf: no match.
- rg for vanishingIdeal/reduced_induced in lean/Sheaf: no complete existing statement.

The theorem docstring carries all nine proof steps with their node names, including
basis localization, construction, reducedness, and both parts of uniqueness.
Server single-file compilation: clean, 1.8 seconds, exit 0. Delivery dry run is the final check.

## Second reading by H1

I independently read the node, all six statement-dependency nodes and the actual
recorded declarations, the delivered module, and the source. The cited local
Stacks TeX is absent. I obtained the official `stacks/stacks-project` `schemes.tex`
in this item's scratchpad and read `lemma-reduced-closed-subscheme`, its entire
proof, `definition-reduced-induced-scheme`, and the surrounding reduced-schemes
section; I also checked official pages https://stacks.math.columbia.edu/tag/01J3
and https://stacks.math.columbia.edu/tag/01J4. There is no standing finiteness,
Noetherian, separation, base-field, or characteristic hypothesis.

Object/hypothesis/clause inventory and comparison (H3):

1. Ambient scheme X: `(X : Scheme.{u})`. The dependency `def-pc-scheme`
   records Mathlib's locally affine locally ringed space `Scheme`, and its
   morphisms are `Scheme.Hom`, not merely continuous maps. Verdict: exact.
2. Closed subset T of X: `(T : TopologicalSpace.Closeds X)`. Closedness is
   bundled; no additional condition is imposed on T or X. Verdict: exact.
3. Every open U and section f, and every point in T intersect U: the first
   conjunct binds `(U : X.Opens) (f : Γ(X, U))`, then `(t : X) (ht : t ∈ U)`
   and `t ∈ T`. Its equality uses `X.evaluation U t ht f = 0`. I opened
   `residueField`, `residue`, `evaluation`, and `Hom.residueFieldMap` in
   Mathlib's ResidueField file: evaluation is exactly germ followed by the
   quotient of the local ring by its maximal ideal. Verdict: exact, including
   all nonaffine opens and no evaluation outside the domain of a section.
4. The ideal sheaf I_T: `f ∈ (vanishingIdeal T).idealOfOpens U ↔ ...` identifies
   its sections with precisely the pointwise prescription. The imported
   upstream `idealOfOpens` is the kernel of `J.subschemeι.app U`; `toModules`
   is the sheaf kernel and its inclusion has range `idealOfOpens U` on EVERY
   open. This is an actual subsheaf, not just unrelated ideals. Verdict: exact.
5. Clause (1), quasi-coherent sheaf of ideals: `vanishingIdeal T` has type
   `X.IdealSheafData`. I read the structure in Mathlib IdealSheaf.Basic:
   it has affine ideals and `map_ideal_basicOpen`, precisely the agreed
   dependency encoding of quasi-coherent ideal sheaves. This encoding and
   the existing sheaf-kernel bridge in item 4 establish the intended notion;
   no private quasi-coherence predicate or second ideal sheaf is introduced.
   Verdict: exact under the dependency's recorded representation.
6. Clause (1), affine ideal and radical uniqueness: `∀ U : X.affineOpens`
   followed by `∃! I : Ideal Γ(X, U), I.IsRadical ∧ ...` identifies the zero
   locus with `U.2.fromSpec ⁻¹' (T : Set X)`. `fromSpec` is the affine chart
   Spec Γ(X,U) → X, so this preimage is T intersect U in chart coordinates.
   The next equality identifies `(vanishingIdeal T).ideal U` with the
   prime-spectrum vanishing ideal of the same closed set. That ideal is
   radical with this zero locus and is therefore the unique I just quantified.
   `idealOfOpens_eq_ideal` identifies it with I_T(U), not a different ring.
   Verdict: exact; the conjunctions concern the same canonical ideal.
7. Clause (1), restriction I_T|_U equals tilde I: the basic-open conjunct is
   `(I.ideal U).map (X.presheaf.map ...).hom = I.ideal (X.affineBasicOpen g)`
   for EVERY g. Sections on D(g) are the localized ideal, and restrictions
   are the ambient structure-sheaf restrictions; these determine the same
   subsheaf on the basic-open basis. Together with item 4 this renders equality
   as ideal subsheaves, not just an abstract module isomorphism. Verdict: exact.
8. Clause (2), closed subscheme cut out by I_T: the chosen morphism is
   `(vanishingIdeal T).subschemeι`; `IsClosedImmersion ...` and
   `...subschemeι.ker = vanishingIdeal T` state its defining ideal. I read
   `Hom.ker` and `ker_apply`: for closed immersions (which are quasi-compact)
   the affine ideals are the actual section-map kernels, matching
   `def-sbc-closed-immersion-ideal-sheaf`. Verdict: exact.
9. Clause (2), reducedness and image: `IsReduced ...subscheme` and
   `Set.range ...subschemeι = (T : Set X)`. I read `IsReduced` and its stalk
   equivalence: this is the dependency's reduced scheme, without assuming X
   itself reduced. Closed immersion means closed embedding and surjective
   stalk maps, exactly the dependency's scheme morphism notion. Verdict: exact.
10. Clause (2), local quotient morphism: `∀ U : X.affineOpens, IsPullback ...`
    has top arrow `subschemeCover.f U`, left arrow `Spec.map` of the quotient
    map, right arrow `subschemeι`, and bottom arrow `U.2.fromSpec`. I read
    `Spec`, `Spec.map`, `subscheme`, `subschemeι`, and `subschemeCover`:
    the source of the top arrow is DEFINITIONALLY Spec(Γ(X,U)/I(U)). Thus
    this says the inverse image of U is the quotient spectrum OVER U, with
    the correct map, and does not assert an unrelated abstract isomorphism.
    Verdict: exact.
11. Clause (3), other closed immersion: `∀ (Z' : Scheme.{u}) (i' : Z' ⟶ X)
    [IsClosedImmersion i'] [IsReduced Z'], Set.range i' = T → ...`.
    These are exactly the node's three conditions on the other subscheme,
    with no extra finiteness or affine hypothesis. Verdict: exact.
12. Clause (3), both conclusions: `i'.ker = vanishingIdeal T ∧ ∃! φ :
    Z' ≅ ...subscheme, φ.hom ≫ ...subschemeι = i'`. The kernel equality is
    equality of ideal sheaves in the recorded encoding. Unique isomorphism
    is quantified only after choosing Z' and i', and composition means
    i_T after φ. Verdict: exact, including uniqueness over X.
13. The name of the resulting closed subscheme is supplied by the docstrings
    using the existing construction; the naming sentence calls for no new
    data or new definition. Verdict: exact.

Edge cases: X empty, U empty, and the zero ring on an empty affine open are
allowed. For T empty the pointwise condition is vacuous and the ideal is the
unit ideal (checked against `vanishingIdeal_bot`); its quotient spectrum is
empty. For T = X it is the nilradical (checked against `vanishingIdeal_top`),
so the conclusion is the reduction even when X is nonreduced. Zero sections,
proper closed subsets, and arbitrary nonaffine opens remain covered. There is
no index set or n in this statement and no characteristic restriction. The
explicit arbitrary universe u binds X, Z', section rings, residue fields and
quotient spectra in the usual single-universe category of schemes; no smaller
independent test universe or unbound parameter occurs.

Independent H4 searches, using different wording from the first reader:

- `msearch.py ... leanfinder` query: "sections whose values in residue fields
  vanish on a closed set form a quasi-coherent ideal sheaf, defining the unique
  reduced closed subscheme". Eight hits: vanishingIdeal, ofIdealTop,
  IdealSheafData, mkOfMemSupportIff, subscheme and support-related declarations.
  I opened the relevant definitions; none states the complete node.
- `msearch.py ... loogle` query: `"idealOfOpens"`: zero hits.
- `msearch.py ... leansearch` query: "the vanishing ideal of a closed subset of
  a scheme evaluated on every open equals the functions vanishing in all
  residue fields and defines a unique reduced closed subscheme": service
  unavailable (Internal Server Error), recorded without a mathematical verdict.
- `msearch.py ... grep` query:
  `idealOfOpens|ker_eq_vanishingIdeal|isReduced_subscheme_vanishingIdeal|reduced_induced_closed_subscheme`:
  zero Mathlib hits. Direct `rg` with vanishingIdeal, reducedness, kernel,
  idealOfOpens and unique-isomorphism vocabulary across Mathlib IdealSheaf,
  upstream WeilConjectures and project lean/Sheaf found building blocks only.
  I opened the upstream `Hom.ker_eq_vanishingIdeal` (kernel equals vanishing
  ideal of the closure of the image for a reduced source) and
  `isReduced_subscheme_vanishingIdeal` (reducedness alone). Neither states
  the arbitrary-open characterization, all affine descriptions and uniqueness
  together. The project `exists_idealSheafData_support_eq` in ClosedSubsetQcIdeal
  only supplies an ideal with prescribed support. No complete existing
  declaration requires dropping this module; every notion used already exists.

H5/H6/H8/H9: no new definitions or hidden sorry data; the single theorem ends
in `by sorry` and nothing is proved. The declaration docstring supplies all nine
node proof steps with their dependency ids; module and declaration docstrings
both name the source and blueprint id. Imports are used, the namespace is
upstream-compatible, all lines are at most 100 characters, and every variable
and universe is explicitly bound. I checked `lean.statement` is character-for-
character the declaration signature before `:= by`, not merely normalized.
No new definition nodes, dependency replacements, or statement correction
occur in this delivery, so H12/H13 and correction-citer checks are inapplicable.

Mismatches found: none. Changed only this report by appending the independent
second reading; the Lean module and node signature are preserved. Recompiled
with `scompile.py` using the absolute sandbox module path: clean, exit 0,
1.8 seconds, no warnings. The initial relative-path invocation was corrected
before compilation; it did not modify any source file.
