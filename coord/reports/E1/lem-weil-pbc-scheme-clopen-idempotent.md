## Worker report

The module defines `AlgebraicGeometry.idempotentOpen`, the set of points where a global
section has nonzero stalk germ, and states `AlgebraicGeometry.scheme_clopen_idempotent`.
Its first clause gives equality with the one-germ locus, openness, closedness, and the
complement for `1 - e`. The second gives injectivity on idempotent sections and
surjectivity onto open-and-closed subsets. The next clause spells out the inverse as the
unique idempotent whose germs are one on a subset and zero off it. The final clause gives
idempotence and inverse-image compatibility under `g.appTop`.

The dependency is Mathlib `AlgebraicGeometry.Scheme` / `Scheme.Hom`. Global sections use
`Γ(X, ⊤)`, germs use `X.presheaf.Γgerm`, clopen subsets use `IsOpen` and `IsClosed`, and
pullback uses `g.base ⁻¹'`. All variables and universes are explicit. The theorem has the
single expected `sorry`; the auxiliary definition has no proof data.

Edge cases checked: empty and full clopen subsets, `e = 0` and `e = 1`, empty schemes,
and arbitrary morphisms are all admitted by the stated types.

Searches recorded in the node (LeanSearch, LeanFinder/Loogle, and grep) found only affine
`PrimeSpectrum.isIdempotentElemEquivClopens`; no scheme-level declaration exists. Source
grep found only the closed connectedness theorem in slopmaster2, which is weaker and not
this bijection. No project declaration matched.

## Earlier second reading (a previous round; superseded)

The Lean file and node were read independently. The binders match the scheme, global
section, idempotence, clopen, and morphism data in the node. The four conjunctions render
(a), (b), and (c) clause by clause; the inverse is expressed by stalk-germ values on the
subset and its complement, which is the stated restriction condition. No mismatch was
found.

## Second reading by E1

Independent reading of the node, the full Lean file, the dependency node
`def-pc-scheme`, and its recorded Mathlib declarations. No statement correction, new
node, or dependency module is present. The previous second-reading paragraph is
superseded by this detailed reading.

Objects, hypotheses, and conclusions (each verdict: exact):

- Arbitrary scheme X: `(X : Scheme.{u})`; Mathlib's `Scheme` extends
  `LocallyRingedSpace` with local affine charts. The recorded dependency also provides
  `Scheme.Hom`, the morphisms used by `Y ⟶ X`. No connectedness, nonemptiness,
  finiteness, separatedness, or base ring hypothesis is introduced.
- Global function e and idempotence: `(e : Γ(X, ⊤))`, `IsIdempotentElem e`.
  These are the structure-sheaf global sections and the equation e * e = e.
- U_e: `idempotentOpen e := {x | X.presheaf.Γgerm x e ≠ 0}`. Read the
  Mathlib `Γgerm` signature: it maps sections on top into the stalk at x.
  The definition is actual set data, with no sorry or proof obligation.
- (a) One-germ equality: `idempotentOpen e = {x : X | ... = 1}`;
  openness and closedness: `IsOpen ... ∧ IsClosed ...`;
  complement: `idempotentOpen (1 - e) = (idempotentOpen e)ᶜ`.
  The last equality is the symmetric orientation of the node's equality.
- (b) Bijection: `Function.Injective` on the subtype of idempotents, and
  `∀ U : Set X, IsOpen U ∧ IsClosed U → ∃ e, IsIdempotentElem e ∧ ... = U`.
  Together with (a), these give exactly a bijection onto clopens; the unbundled
  encoding does not omit that the image is clopen.
- (b) Inverse: `∀ U : {U : Set X // IsOpen U ∧ IsClosed U}, ∃! e`, with
  germ one on U and germ zero outside U. By restriction/germ compatibility and
  sheaf section extensionality on each open, these conditions say exactly that
  restrictions are one and zero. Idempotence in this conjunction does not weaken
  uniqueness among all sections: any section with these restriction values is
  idempotent by sheaf extensionality, or by the product-ring decomposition.
  The earlier existence clause ties this unique section to U_e = U.
- (c) Arbitrary Y, g, e: `∀ {Y : Scheme.{u}} (g : Y ⟶ X) (e : Γ(X, ⊤)),
  IsIdempotentElem e → ...`. Read `Scheme.Hom.appTop`: it is precisely the
  structure-sheaf map on top. The conclusion asserts both
  `IsIdempotentElem (g.appTop e)` and the locus equality with
  `g.base ⁻¹' idempotentOpen e`, with e chosen after g as in the node.

Source reading: the local literature checkout has no Stacks .tex, so fetched the
upstream algebra.tex and schemes.tex into this item's scratchpad and read the
labelled lemmas. Algebra Tag 00EE assumes only a ring, including the zero ring;
no Noetherian assumption is inherited. Schemes Tag 01I5 assumes affineness of
its pieces for its affine conclusion, but its first proof step, the product
of section rings, uses only the sheaf property. The node uses that step only,
not that lemma's affine conclusion. Thus the extension to arbitrary schemes
has exactly the hypotheses stated. Sources:
[00EE](https://stacks.math.columbia.edu/tag/00EE),
[01I5](https://stacks.math.columbia.edu/tag/01I5).

Edge cases: empty X is allowed (its global section ring is the zero ring and
there is one clopen subset); no Nonempty instance is assumed. Empty U and
full U give respectively zero and one, with vacuous germ conditions on the
empty part. e = 0 and e = 1 have the expected loci. Characteristic two causes
no problem for 1 - e. No index or natural-number parameter occurs. The arbitrary
universe u covers schemes in any size; Y and X are in the common universe of
the recorded category of schemes, with no smallness instance or test-scheme
quantification in a smaller independent universe. Every binder is explicit.

Independent searches with alternate terms: LeanFinder query "Scheme global
functions clopen subsets characteristic section bijection" returned eight
PrimeSpectrum affine results, including `isIdempotentElemEquivClopens` and
`existsUnique_idempotent_basicOpen_eq_of_isClopen`; none is the scheme statement.
Loogle `AlgebraicGeometry.Scheme, IsIdempotentElem` returned zero hits.
LeanSearch query "Characteristic global section of open closed subset arbitrary
scheme and uniqueness" was unavailable (Internal Server Error); no verdict is
inferred from that service failure. Local rg of clopen/Clopen and idempotent
names in Mathlib algebraic geometry/ringed spaces, source WeilConjectures,
and project lean/Sheaf found no existing declaration of this correspondence.
Opened source `Scheme.connectedSpace_iff_isIdempotentElem`: it assumes Nonempty
and states only the connectedness criterion, although its proof constructs the
same clopen characteristic sections. It cannot replace this module. Mathlib's
`Scheme.basicOpen` is the unit-germ locus, not the nonzero-germ locus of an
arbitrary section; these coincide for idempotents by (a), not definitionally.
Hence `idempotentOpen` is the explicit U_e introduced by this node, not a
private replacement of the dependency or a second general basicOpen definition.
No conflicting declaration name was found.

Mismatches repaired: H8 module documentation, source places in both declaration
docstrings, and the complete five-step natural-language proof were missing.
Added the standard copyright header and those docstrings. Removed two redundant
imports; Mathlib.AlgebraicGeometry.Scheme alone compiles. No mathematical
signature or node field changed. Checked `lean.statement` verbatim against the
file signature. Only the named theorem contains sorry; nothing is proved.
The repaired module compiled on the server with exit 0 and no warnings.
