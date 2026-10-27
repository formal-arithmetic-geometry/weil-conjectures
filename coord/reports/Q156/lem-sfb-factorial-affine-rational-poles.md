## Worker report

The module `Sheaf.AlgebraicGeometry.FactorialAffineRationalPoles` states
`AlgebraicGeometry.exists_effectiveCartierCenter_compl_affine_extension_locus`, with
`sorry` as its sole proof. It introduces no definition or helper theorem. The node
is unchanged except for its `lean` record.

Clause-by-clause reading:

- The field is `(k : Type u) [Field k]`.
- The k-scheme is `W : Over (Spec (.of k))`, with structural map `W.hom`.
  `[IsIntegral W.left]` includes nonemptiness and integral affine coordinate rings;
  it also supplies domain stalks. No additional nonemptiness hypothesis is needed.
- Noetherianness is precisely `[IsLocallyNoetherian W.left]` together with
  `[CompactSpace W.left]`, as the node specifies.
- `hfactorial : ∀ w : W.left, UniqueFactorizationMonoid
  (W.left.presheaf.stalk w)` states factoriality at every local ring. Combined with
  the domain instances for integral schemes, this is the UFD hypothesis, rather
  than the stronger requirement that all affine coordinate rings be UFDs.
- The finitely generated commutative k-algebra is `(A : Type u) [CommRing A]
  [Algebra k A] [Algebra.FiniteType k A]`. The target is literally `Spec (.of A)`.
  Its structural morphism is `Spec.map (CommRingCat.ofHom (algebraMap k A))`.
- The dense open subscheme is `(H : W.left.Opens)` with
  `hH : Dense (H : Set W.left)`; its scheme is `H.toScheme`.
- `h : H.toScheme ⟶ Spec (.of A)` is the given map. The equation `hh` says its
  composite with the target structural map is `H.ι ≫ W.hom`, exactly “over k”.
- The set inside `sSup` consists of all `V : W.left.Opens` for which there exists
  `hV : V.toScheme ⟶ Spec (.of A)`. Its first conjunct says `hV` is over k.
  Its second conjunct compares `W.left.homOfLE inf_le_left ≫ hV` with
  `W.left.homOfLE inf_le_right ≫ h`, both from `(V ⊓ H).toScheme`. Thus agreement
  is on all of `V ∩ H`. There is no requirement that `V` contain `H`.
  The coercion of `sSup` to a set is exactly the union E in the node.
- The conclusion quantifies a scheme `P` and `i : P ⟶ W.left` with
  `IsEffectiveCartierCenter i`, the recorded effective Cartier divisor predicate.
  This forces `i` to be a closed immersion and its ideal to be locally generated
  by one nonzerodivisor. `Set.range i` is its underlying closed subset.
- The final equality is exactly `Set.range i = Eᶜ`. There is no nonemptiness
  requirement on P, so the empty divisor is allowed. No properness condition on
  the target and no separatedness condition on the source occurs.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs (mathlib_match).
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  Mathlib.AlgebraicGeometry.Properties, including `IsIntegral.nonempty` and
  `IsIntegral.component_integral`.
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian`,
  Mathlib.AlgebraicGeometry.Noetherian.
- `def-weil-pbc-quasi-compact-scheme`: `CompactSpace`,
  Mathlib.Topology.Defs.Filter; no Hausdorff condition is included.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme.
- `def-pc-divisor-line-bundle`: the recorded
  WeilConjectures.AlgebraicGeometry.EffectiveCartier interface, specifically
  `AlgebraicGeometry.IsEffectiveCartierCenter` and
  `AlgebraicGeometry.isEffectiveCartierCenter_iff_isInvertible_ker`. Its definition
  is in WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier;
  `Scheme.IdealSheafData.IsInvertible` in the upstream Invertible module is the
  affine-local nonzerodivisor-generator condition. The line bundle itself does not
  occur in this node's assertion.

Additional standard interfaces are `Algebra.FiniteType` in
Mathlib.RingTheory.FiniteType, `UniqueFactorizationMonoid` in
Mathlib.RingTheory.UniqueFactorizationDomain.Defs, and `Scheme.homOfLE` in
Mathlib.AlgebraicGeometry.Restrict. All binders and the universe `u` are explicit,
with `set_option autoImplicit false`.

The recorded, stated proof dependencies are imported privately: ideal products
(Mathlib.AlgebraicGeometry.IdealSheaf.Basic), meromorphic modules
(Sheaf.AlgebraicGeometry.MeromorphicModule), module stalks
(WeilConjectures.Topology.PresheafModuleStalkFunctor), the affine adjunction
(Mathlib.AlgebraicGeometry.GammaSpecAdjunction), denominator ideals
(Sheaf.AlgebraicGeometry.MeromorphicDenominatorIdeal), integral function fields and
stalks (Mathlib.AlgebraicGeometry.FunctionField), closed subschemes of ideal sheaves
(Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme), and tilde stalk localization
(Mathlib.AlgebraicGeometry.Modules.Tilde). Scheme sobriety is in the public
Properties module. The proof dependency
`lem-sfb-stalk-nonzerodivisor-cartier-spreading` has no recorded declaration or
Mathlib match in the read clone, so it has no import at this stage; it is named in
the proof docstring and is not needed to type this statement.

Source checks: read Milne AV I, Lemma 3.3 and its polar-divisor argument (printed
pp.17–18), and Stacks Divisors `lemma-weil-divisor-is-cartier-UFD` (0AGA) and
`lemma-effective-Cartier-in-points` (0AG8), including their proofs. This node is an
explicit finite-coordinate generalization, as its proof_origin already records.
The seven-step proof is reproduced in the theorem docstring without asserting
that Milne states this full generality verbatim.

Edge cases checked before writing:

- An integral scheme is nonempty. Hence a dense open is nonempty and contains
  the generic point; an empty H cannot accidentally enter the theorem.
- A = k has an empty algebra generator family: its structural map extends
  everywhere, E is W, and the conclusion allows P empty.
- A zero rational coordinate has unit denominator ideal; it produces no polar
  component. If all coordinates are regular, again E is W and P may be empty.
- H = W is allowed. Every restriction of h is an extension on its open, so E = W.
- Empty candidate opens are allowed: their inclusion in the union has no effect.
- The zero algebra A is not excluded syntactically. No map from the nonempty
  dense open into its empty spectrum exists, which correctly makes this input
  case impossible rather than adding a nontriviality hypothesis on A.
- W need not be separated, and the conclusion requires no multiplicity or
  reducedness of the divisor beyond being an effective Cartier divisor.

Searches (2026-10-24), using the prescribed msearch.py wrapper:

- LeanFinder: “The extension locus of a rational morphism from a locally
  factorial integral Noetherian scheme to an affine scheme has effective Cartier
  complement”. Eight hits, led by `Scheme.RationalMap.domain`,
  `RationalMap.fromFunctionField`, `RationalMap.ofFunctionField`, and partial-map
  interfaces. None asserts a Cartier complement.
- LeanSearch: “The complement of the extension locus of a rational map to an
  affine scheme on a locally factorial integral scheme is an effective Cartier
  divisor”. Eight hits, including rational maps and their domains, unramified
  loci and zero loci. No theorem matches this assertion.
- Loogle: `"IsEffectiveCartierCenter"`: zero hits.
- Mathlib grep, AlgebraicGeometry:
  `extensionLocus|extension_locus|factorial.*[Pp]ol|rational.*[Pp]ol`: zero hits.
- Direct rg of WeilConjectures and Sheaf for the item id and for
  `extensionLocus|extension_locus|factorial_affine|affine.*rational.*[Pp]ol`:
  only the already-landed group indeterminacy theorem mentions this item in its
  proof docstring; no declaration states it.
- Direct rg for factorial stalks found existing UFD interfaces, and inspection
  of WeilConjectures.AlgebraicGeometry.Divisor.AffineComplement found
  `Scheme.exists_isInvertible_support_eq_compl`: this concerns a nonempty affine
  OPEN of a separated Noetherian integral scheme. The present extension domain
  is not assumed affine and W is not assumed separated, so that is not a match.
  CartierExtensionFactorialComplement likewise extends a given Cartier divisor
  across a factorial complement, a different assertion.

No node fault, disputed statement, new node or dependency repair was found.

## Second reading by Q156

The dispatcher explicitly assigns one worker and forbids starting other agents;
this section records a separate self-review, not an independent second worker.
The maintainer's independent review is still required by the delivery brief.

Rereading the node and the complete signature together confirms the six
hypotheses (field/base, nonempty integral, Noetherian, factorial stalks, finite-type
commutative algebra, dense-open k-morphism), the precise union over compatible
local extensions, and the effective Cartier divisor with exactly that complement.
In particular, the comparison maps have common source V ∩ H, not just a smaller
dense open; the set is a supremum of opens, not the original domain; and
`IsEffectiveCartierCenter` supplies a genuine closed immersion with the stated
nonzerodivisor condition. The empty divisor and zero-generator cases remain.
There is one theorem, no duplicate notion, no auto-bound implicit, no statement
correction, and the seven proof steps remain in its docstring. The initial compiler
check showed that the recorded umbrella module does not publicly expose
`IsEffectiveCartierCenter` in module mode. An explicit public import of its owning
module, WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier,
fixes visibility without changing or replacing the recorded notion.

Validation: scompile.py compiled the delivered file in sandbox and library mode
against the published live build, cleanly (2.1 s and 2.3 s). The only source change
after the initial failed check was the public import described above.
