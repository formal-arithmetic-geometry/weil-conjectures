## Worker report

The delivery states the ordinary-etale Fourier–Deligne transform for exactly the general
coefficient and geometric data of sk-def-kernel. The real composite and its public
abbreviation are defined together in
Sheaf.FourierTransform.FourierDeligneTransform, owned exclusively by sk-def-ft. The
composite uses the existing derived operations specified by def-fd-transform. The live
def-fd-transform node and its 24-declaration record are unchanged. The item retains its
statement verbatim; no theorem is proved and no new sorry, axiom, arbitrary map or choice of kernel is introduced.

Hypotheses and clauses of sk-def-ft, in order:

- The coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ]`, with a prime
  `{p : ℕ} [Fact p.Prime]` and `[Invertible (p : Λ)]`, as inherited from sk-def-kernel.
  The universe convention is the existing small-etale ModuleCat convention.
- The schemes and the two structure maps are `{S V V' : Scheme.{u}} (π : V ⟶ S)
  (π' : V' ⟶ S)`. The product is `pullback π π'`, and its projections are
  `pullback.fst π π'` and `pullback.snd π π'`.
- The inherited characteristic condition is precisely
  `(h : (p : Γ(pullback π π', ⊤)) = 0)`. It is not `CharP` of that ring.
- The character and pairing are `(Ψ : AddChar (ZMod p) Λ)` and
  `(b : Γ(pullback π π', ⊤))`. AddChar expresses multiplicativity with respect to
  addition and sends zero to one. Its values are automatically units (the value at
  minus the input supplies the inverse); it admits the trivial character.
- The supplied kernel is the dependency's exact
  `AlgebraicGeometry.Etale.fourierKernelOfNatCastEqZero Λ π π' h Ψ b`.
  `DerivedCategory.singleFunctor _ 0` places that sheaf in degree zero.
- Compactifiability and the chosen compactification are expressed together by
  `(c : Compactification (pullback.snd π π'))`. This is exactly the chosen data required
  in the node, not an extra restriction on a compactifiable morphism. Its `i` is an open
  immersion, its `g` is proper, and `c.comm` gives the factorization. There is no
  quasi-compactness assumption on `c.i`.
- The shift parameter is `(r : ℤ)`, with no nonnegativity assumption.
- The source and target are the unbounded `DerivedCategory` of
  `Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)` and the same expression with `V'`.
  These are ordinary module-valued etale sheaves, not the adic common-stage category.
- Pullback is `D((pullback.fst π π')^*[ModuleCat.{u + 1} Λ])`, the existing functor
  induced by the exact inverse image of module sheaves.
- Tensor is `derivedTensorRight (ModuleCat.{u + 1} Λ) (pullback π π')` evaluated at
  that degree-zero kernel. This tensors the pulled-back complex on the right with the
  fixed kernel, in the order of the displayed formula.
- Compact-support pushforward is
  `rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c`, whose existing
  body is `D(c.i_!) ⋙ R(c.g_*)`; it is not a right derived functor of the underived
  composite `c.i_! ⋙ c.g_*`.
- The final `shiftFunctor _ r` is the existing cochain shift: the degree-i term comes
  from degree i+r and the differential has the usual sign. Composition with `⋙` gives
  the stated functor on all objects and all morphisms, including the identity on the
  tensor kernel in its action on a morphism.
- The node's sentence assigning every operation and morphism map to def-fd-transform
  is rendered by the composite of those existing operations, with the item's abbreviation
  unfolding to it on objects and morphisms.
- The vector-bundle and dual application specializes these arbitrary scheme morphisms,
  takes evaluation as `b`, and takes the integer rank as `r`. No vector-bundle hypothesis
  is imposed on the general transform. On the affine line this is `b = x ξ`, `r = 1`.
  Applying the same construction to `Ψ⁻¹` gives the inverse-character transform.
  These specializations are explained in both declaration docstrings, as in the node.

Dependency declarations used and source signatures read:

- sk-def-kernel: Sheaf.FourierTransform.KernelNatCastEqZero,
  `AlgebraicGeometry.Etale.fourierKernelOfNatCastEqZero`. Its full signature has arbitrary
  commutative Λ, p prime and invertible, the two scheme maps, h, Ψ, b, and returns the
  ordinary module-valued etale sheaf. Its body is
  `artinSchreierSheafOfNatCastEqZero h Ψ b`. Its docstring specifies the prime-field
  kernel, the empty-product case and the evaluation/affine-line specializations.
- def-fd-transform: the prior record was read in full in
  Sheaf.Paper.CommonStageFourierTransform. Its primary declaration is the adic
  `WeilConjectures.commonStageFourierTransformFunctor`, and its extra declarations retain
  the old ordinary `Etale.fourierTransform`. Neither gives the general node exactly.
  Its record is preserved byte-for-byte: CommonStageFourierTransform is publicly
  imported, while the general ordinary-etale composite is owned by sk-def-ft itself.
- Existing operations, with full signatures and definitions inspected:
  `AlgebraicGeometry.Etale.upperStar` in
  WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs (sheaf inverse image);
  `CategoryTheory.Functor.mapDerivedCategory` from the existing exact-functor API;
  `AlgebraicGeometry.Etale.derivedTensorRight` in
  WeilConjectures.SixFunctors.Etale.Derived.Tensor (right tensor with a fixed derived
  sheaf); `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification` in
  WeilConjectures.SixFunctors.Etale.Derived.LowerShriek (D of extension by zero,
  then the unbounded total right derived direct image); and
  `AlgebraicGeometry.Compactification` in WeilConjectures.Compactification.Defs.
  These reuse the derived category, exact extension by zero, direct image, and
  K-injective machinery of the detailed node rather than defining private versions.
  ConcreteCoefficients supplies the existing module-category coefficient instances.

Edge cases checked before writing:

- Empty product W: its global ring is the zero ring, so h holds, while `CharP _ p`
  would exclude it for prime p. Neither new declaration requires `CharP` or `Nonempty W`.
- Empty source, target, or base is not excluded by any binder.
- Zero coefficient ring is allowed: p is invertible there and AddChar still makes sense.
  No `Nontrivial Λ`, field, finiteness or torsion assumption was added.
- p = 2, trivial Ψ, b = 0, r = 0, negative r and rank zero are all included.
- Arbitrary compactification, including a non-quasi-compact open immersion, is accepted
  by the exact existing Compactification structure and lower-shriek construction.
- Zero complexes and all morphisms are handled by functor composition, not by an
  object assignment requiring an unrecorded functoriality theorem.

Searches actually run:

- msearch.py leanfinder, query "Fourier Deligne transform on derived categories etale
  module sheaves pullback derived tensor kernel compactification shift": eight hits,
  including Scheme.Modules.pullback and SheafOfModules.pullbackComp; none is this transform.
- msearch.py loogle, query "fourierTransform, kernelTransform": zero hits, diagnostic
  "unknown identifier 'fourierTransform'". This is not evidence of absence upstream;
  the explicit project search below found the actual upstream construction.
- msearch.py leansearch, query "Fourier Deligne transform as functor between derived
  categories of etale sheaves": eight analytic Fourier-notation hits, no etale transform.
- msearch.py grep, query "fourierTransform|kernelTransform", subdirectory
  AlgebraicGeometry: zero Mathlib hits.
- rg and grep of lean/WeilConjectures found the full FourierTransform.Defs definition
  and its sk-def-ft docstring. It uses `[CharP Γ(pullback π π', ⊤) p]`, so fails the empty
  product case. The generic kernelTransform also exists but takes an arbitrary derived
  kernel, rather than supplying this node's prime-field Artin–Schreier kernel.
- rg of lean/Sheaf found the adic CommonStageFourierTransform and WeilFourierTransform
  specializations, and the newly landed exact KernelNatCastEqZero construction. No exact
  general transform with the permitted empty product was found. The new declaration
  names were searched in Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json.

The main-20261015 unit and detailed blueprint text were read in full. The detailed node's
current statement gives the precise chosen-compactification convention, followed by the
composite owned by sk-def-ft without changing the detailed node's record. No statement
correction or disputed mathematical statement is needed.

## Returned-delivery repair: H13 and H4

The returned immutable head d0e0d194d8f6 replaced def-fd-transform's live Q24 record
and dropped ownership of CommonStageFourierTransform and its 24 declarations. The saved
packet's first dry run passed (3223e8ab297), but the independent return identifies a
semantic ownership failure that mechanical preflight does not detect.

The repair takes the maintainer's first authorized option: the actual four-factor
composite `fourierTransformOfNatCastEqZero` now lives in the item's sole module,
Sheaf.FourierTransform.FourierDeligneTransform, alongside `fourierDeligneTransform`.
Both declarations carry sk-def-ft source docstrings and are listed in the item's
lean.declarations. The separate TransformNatCastEqZero module is removed from the
packet. The def-fd-transform node copy is removed from the packet, leaving its live
record, all 24 attached declarations, module and landed C9 proofs untouched.
CommonStageFourierTransform is publicly imported by the item.

No existing consumer needs an edit: FourierTraceFormula (sk-thm-fourier-trace-formula),
CommonStageCurveWeilMiddleExtension (def-wf-middle-extension), FourierKernelConvolution
(lem-fd-convolution-kernel), and CommonStageFourierWeightUpper
(prop-a1-fourier-weight-upper) all keep the same module and declaration owners.
No dependency module, new node, statement correction, or stmt_deps change is delivered.
The mathematical data, hypotheses, composite order, and edge cases are unchanged.

## Validation

The repaired sole module compiled via scompile.py in both sandbox and library modes
without errors or warnings (3.5 s each). Self-check confirmed that only the item's lean
field differs from the live item, the stored statement signature occurs verbatim in the
file, every Lean line is at most 100 characters, and the packet contains exactly one
module and one node. No dependency node is included. All variables and universes are
explicitly bound; `set_option autoImplicit false` is enabled. The only new data is the
actual composite, and the item's abbreviation unfolds to it. Independent review is left
to the maintainer, as required by the dispatch brief.

## Second reading by NZ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
