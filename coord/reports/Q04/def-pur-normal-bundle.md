## Worker report

The delivery defines the actual normal cone of the given closed immersion, its affine
projection, its degree-zero augmentation section, and, for a regular immersion of pure
codimension c, its canonical rank-c vector-bundle structure and equality of zero sections.
The main module is `Sheaf.Paper.PurityNormalBundle`. All theorem proofs are `sorry`;
all definitions contain real terms. Three modules and three node records are supplied.
No statement, dependency list, proof, source, or status is changed.

Clause-by-clause correspondence for `def-pur-normal-bundle`:

- The fixed purity setting is `P : WeilConjectures.PurityFiniteSetting.{u}` in the regular
  assertion and bundle construction. Its field is exactly `P.field.k`. The algebraic cone
  construction itself is independent of the coefficient data, and is defined for every
  closed immersion, as in the node's first two proof steps.
- Schemes and the closed immersion are `{X Z : Scheme.{u}}`, `i : Z ⟶ X`, and
  `[IsClosedImmersion i]`. The field structure maps are `hX` and `i ≫ hX`.
  `[IsSeparated ...]`, `[LocallyOfFiniteType ...]`, and `[QuasiCompact ...]` on both maps
  express the separated finite-type hypotheses of the regular-immersion dependency.
- The defining ideal is precisely Mathlib's `i.ker`, not an independently supplied ideal.
  Its module and inclusion are the upstream `i.ker.toModules` and `i.ker.toModulesι`.
  The shared `Scheme.idealSheafPower` constructs the powers by actual images of ideal
  multiplication; its affine range is `(i.ker.ideal U)^n`, including n=0 and n=1.
  `Presentation.powerIdentification` explicitly identifies it, preserving the inclusion,
  with the recorded ideal-sheaf-power declaration `(i.ker ^ n).toModules`.
  `pieceQuasicoherent` records quasi-coherence of every homogeneous module as well.
- `ConormalGradedAlgebra.piece i n` is the tensor pullback of that ideal power. Thus its
  affine module is `I(U)^n / I(U)^(n+1)` on Z. In particular `piece i 1` is definitionally
  `(Scheme.Modules.tensorPullback i).obj i.ker.toModules`, exactly the node's conormal C.
- `ConormalGradedAlgebra.presentation i` supplies the conormal algebra G. Its underlying
  module is characterized by `Presentation.coproduct` as the sheaf coproduct of these
  fixed pieces; `multiplication` and `constants` specify precisely the representative
  multiplication and degree-zero unit. `affineChart` and `stalkChart` identify every
  homogeneous representative with the corresponding associated-graded class.
- `algebraObject i` bundles this exact G with its quasi-coherence. `over i` applies the
  inverse of the anti-equivalence characterized by `affine_morphism_relative_spec`.
  `normalCone i` is its total scheme and `projection i` its affine structural morphism.
  This is the displayed `Spec_Z G`, without a smooth projection supplied as a hypothesis.
- Regularity and pure codimension are `IsRegularImmersionOfPureCodimension hX i c`:
  c >= 1, the specified equality of stalk Krull dimensions, and a length-c regular
  generating sequence of the kernel of each structure-stalk map. These are exactly the
  chapter's convention; the forward pointer to smooth-pair linearization is not extra data.
- `regular_spec` asserts `(piece i 1).IsFiniteLocallyFreeOfRank c` and invertibility of
  the canonical symmetric-to-conormal algebra map. The latter is the node's Steps 4--5
  identification, needed to construct its specified bundle rather than an arbitrary one.
- `vectorBundle i P hX c hreg : PurityVectorBundle P Z (i ≫ hX) c` has total scheme
  definitionally `normalCone i`, projection `projection i`, and conormal module `piece i 1`.
  Its chosen `phi` is the relative spectrum of the canonical symmetric-algebra comparison;
  it is an isomorphism over Z to `Spec_Z Sym(C)`, not a global trivialization.
- `ConormalGradedAlgebra.augmentation i` is the unique algebra morphism fixing degree-zero
  representatives and killing positive degrees. `augmentationToBase` composes it with
  the canonical structure map to the direct-image algebra of the identity Z-scheme.
  `zeroSection i` is its inverse image under the same fully faithful anti-equivalence.
- `zeroSection_spec` states `zeroSection i ≫ projection i = 𝟙 Z` and
  `IsClosedImmersion (zeroSection i)`. `vectorBundle_zeroSection` states literal equality
  of the zero section of the displayed canonical bundle with this augmentation section.

The conormal dependency's full clauses are also represented. `pushforwardPiece` identifies
its direct-image degrees with the shared sheaf cokernels `formalAssociatedGradedPiece`,
with their quotient representative formula; `degreeZero` gives O_Z, and degree one is the
specified tensor pullback. The affine ring charts preserve all homogeneous classes and
therefore the grading. Their restriction compatibility follows from those formulas and
naturality of the homogeneous inclusions and tensor-pullback unit: affine representatives
generate each degree, so there is no freedom to change a transition map. `quotientStalk`
is the actual first-isomorphism equivalence of the surjective structure-stalk map.
`conormalStalk` gives the conormal/cotangent equivalence, with its scalar and germ formulas;
`stalkChart` gives the graded-algebra stalk identification. `symmetricComparison` is chosen
from the unique map extending degree-one inclusion on every open. `symmetricStalk` pins the
symmetric-algebra stalk identification on generators; naturality of this comparison then
says exactly that its stalk sends a cotangent class to that degree-one graded class.
`coherent` asserts coherence of every degree when X is locally Noetherian.

The conormal algebra is selected from a universal-property theorem, as expressly allowed
by AGENTS.md section 5. This is not choice from bare existence of an unspecified object:
the fixed homogeneous modules, coproduct universal property and representative products
uniquely determine the algebra up to the unique inclusion-preserving algebra isomorphism.
`exists_conormalGradedAlgebra` states this unique comparison explicitly. The relative
spectrum uses precisely this algebra, and the comparison and augmentation are each chosen
from unique-existence statements. All downstream equalities use these canonical maps.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting` and its `field`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`;
  also `Scheme.Hom.stalkMap_surjective`, and the affine closed-immersion criterion.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.Hom.ker`,
  `Scheme.IdealSheafData.ideal_mul`, `Scheme.IdealSheafData.ideal_pow`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`:
  `Scheme.IdealSheafData.toModules` and `toModulesι`.
- `Sheaf.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullback`;
  `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`:
  `Scheme.Modules.exists_tensorPullbackAdjunction`, with its explicit canonical unit formula.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`.
- `Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec`: `affine_morphism_relative_spec`.
  The already published `VectorBundleZeroSection.antiEquivalence` is its chosen witness;
  that module's `baseObject` and `algebraObject` are reused as well.
- `Sheaf.Paper.PurityVectorBundleZeroSection`: `PurityVectorBundle` and its `zeroSection`.
- `Sheaf.AlgebraicGeometry.FormalKernelGradedPieces`: `formalAssociatedGradedPiece`,
  `formalAssociatedGradedπ`; its shared ideal-power construction is
  `Scheme.idealSheafPower` from `Sheaf.AlgebraicGeometry.IdealModuleProductStalk`.
- `Sheaf.RingTheory.AssociatedGradedRing`: `Ideal.associatedGraded`,
  `Ideal.associatedGradedPiece`, with their actual direct-sum ring structure.
- `Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction`:
  `SymmetricAlgebraSheaf.algebra` and `inclusion`;
  `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore`:
  `exists_quasiCoherentSymmetricAlgebra_core`.
- Proof imports also include `RingTheory.Sequence.regularSequence_conormal_free`,
  `Scheme.Modules.isFiniteLocallyFree_of_coherent_free_stalks`, and
  `SymmetricAlgebra.equivMvPolynomial`. The remaining proof-only nodes without a recorded
  module (`lem-pur-regular-sequence-graded-polynomial` in particular) have no import yet;
  no import cycle is introduced and no proof is attempted here.

Sources opened: the exact master blueprint definition at order 1894 and the defining
regular-immersion paragraph; Stacks `divisors.tex`, definitions 0630, 0636 and equations
0631, 0632, 0637, affine lemma 0633, and regular/quasi-regular lemma 063M; the normal-cone
and conormal pages were also checked online. The complete blueprint and Stacks text is
available in the launcher's literature mirror although the shared read-only checkout
contains only the literature lists.

Edge cases checked before writing:

- Empty Z: all stalk conditions are vacuous, while the sheaf coproduct and relative Spec
  still define the empty total space. The rank statement and the section remain valid.
- Identity immersion and zero ideal: the graded algebra has O_Z in degree zero and zero
  in positive degrees; the cone and zero section are the identity over Z.
  For a nonempty scheme, positive-codimension regularity of the identity is excluded
  by its zero stalk ideal. On the empty scheme the stalk conditions are vacuous, so
  the empty identity satisfies the definition for every c >= 1; its zero conormal
  module is locally free of every rank on the empty base.
- Empty closed subscheme/unit ideal: all quotient degrees are zero on the empty base;
  the construction still applies without an artificial nonempty hypothesis.
- n=0: the ideal power is literally O_X, constants are specified, and the augmentation
  fixes them. Multiplication with a degree-zero class has its actual scalar formula.
- Nonregular immersion: the cone and augmentation are defined; no locally-free or
  vector-bundle conclusion is asserted without regularity.
- Nontrivial conormal bundle: no global basis is selected. The rank assertion is local;
  `phi` is the canonical symmetric-algebra comparison, not an affine-space isomorphism.
- Universes are explicitly bound to u. There is no independent test-object universe,
  coefficient restriction, perfectness, smoothness or extra Noetherian hypothesis.

Searches (all searches used the prescribed msearch wrapper where applicable):

- LeanFinder, "The normal cone of a closed immersion is the relative spectrum of the
  associated graded ideal algebra": eight hits concerning ordinary closed immersions,
  quotient spectra, ideal-sheaf gluing and normalization, no normal-cone construction.
- Loogle, `"normalCone"`: zero hits. Earlier retained searches `"NormalCone"` also had
  zero hits. Loogle, `"conormal"`: zero hits.
- msearch grep, `normalCone|normalBundle|NormalCone|conormalAlgebra` in
  Mathlib/AlgebraicGeometry: zero hits.
- LeanSearch, "Normal cone of a regular closed immersion as a vector bundle with
  canonical zero section": unavailable (Internal Server Error), as recorded by the tool.
- LeanFinder, "Regular immersion of pure codimension defined by stalkwise Krull dimension
  and regular generating sequence": ring Krull-dimension and regular-sequence localization
  results, standard smoothness, and smooth-relative-dimension results; no exact definition.
- rg of upstream WeilConjectures and shared lean/Sheaf for the normal/conormal names found
  upstream `Scheme.Hom.NormalConeData`. I read its full source and TODO: it does not tie its
  scheme to i, and expresses only smoothness rather than a vector bundle. It is unusable
  for this node. The upstream `IsRegularImmersion` is an affine-local candidate, not the
  chapter's complete stalkwise interface; no recorded declaration existed for that node.
- rg of the DAG and existing algebra modules found the shared ideal-power, formal graded
  piece and associated-graded ring constructions, which are reused, not redefined.
- The current-server `scompile.py --source` checks found no published conormal or purity
  regular-immersion module under the candidate names. I also searched the current server
  source and delivery branch names: the only related branch was Q44's regular-immersion
  stage-1 split, with no Lean record or module. Thus no delivered construction was bypassed.

No STATEMENT-DISPUTED finding and no source-based statement correction is needed.

## Second reading by Q04

I read the node statement (blueprint order 1894), the source paragraph, the three
delivered modules, and every recorded statement dependency. The item-by-item
correspondence is as follows.

- The fixed purity setting is the node's `[def-pur-conventions]` object, rendered by
  `P : WeilConjectures.PurityFiniteSetting.{u}` and used through `P.field.k`; no
  coefficient hypothesis is used to define the cone.
- The objects `X`, `Z`, and `i : Z ⟶ X`, together with the closed-immersion hypothesis,
  are rendered by `{X Z : Scheme.{u}}`, `(i : Z ⟶ X)`, and `[IsClosedImmersion i]`.
  The ideal is exactly `i.ker`, and its powers are the shared
  `Scheme.idealSheafPower i.ker.toModulesι` construction, with the recorded
  inclusion-preserving identification to `(i.ker ^ n).toModules`.
- The displayed graded algebra is rendered by
  `ConormalGradedAlgebra.presentation i`; its `piece i n` is the tensor pullback of
  the actual `n`th ideal power, and the presentation carries the multiplication,
  degree-zero constants, coproduct, and affine/stalk quotient charts required by
  `lem-pur-conormal-graded-algebra`.
- The normal cone and projection are exactly `normalCone i` and `projection i`, obtained
  from the relative-spectrum anti-equivalence. Thus the Lean object is
  `Spec_Z (⨁ I^n/I^(n+1))`, rather than an unrelated normal-cone datum.
- The augmentation and canonical section are `augmentationToBase i` and
  `zeroSection i`. The theorem `zeroSection_spec` gives the section identity and the
  closed-immersion clause represented by the node's `Z ↪ N_{Z/X}`.
- In the regular case, `hX`, its separated/finite-type/quasi-compact instances, the
  corresponding instances for `i ≫ hX`, `c`, and
  `hreg : IsRegularImmersionOfPureCodimension hX i c` render exactly the regular
  pure-codimension hypotheses of the dependency node. `regular_spec` states the
  degree-one conormal local freeness of rank `c` and the canonical symmetric-algebra
  isomorphism; `vectorBundle` packages these as a `PurityVectorBundle` with total
  scheme `normalCone i`, projection `projection i`, and conormal module `piece i 1`.
  Finally `vectorBundle_zeroSection` identifies its zero section with `zeroSection i`.
  The comparison is an isomorphism over `Z`, not a chosen global trivialization.

No hypothesis is added to the cone construction, and the regular-case typeclass
arguments are precisely those required by `def-pur-regular-immersion` and the
`PurityVectorBundle` dependency. Universes are shared at `u`; no independent test
universe or hidden Noetherian, smoothness, characteristic, or nonemptiness assumption
appears. The helper theorem `regular_spec` is an internal statement used to construct
the node's vector-bundle datum; it does not alter the node's signature.

Edge cases were checked: the empty scheme is covered without a nonemptiness
hypothesis; the grading index is all of `ℕ`, including zero. The zero and unit ideals
give the identity and empty-base cone behavior; `n = 0` uses the actual `I^0 = O_X`
constants; the identity immersion is
defined; on a nonempty scheme it cannot satisfy the positive-codimension regular
hypothesis, while on the empty scheme it satisfies that hypothesis for every c >= 1; nonregular
immersions still have a cone and augmentation but no vector-bundle conclusion; and no
global conormal basis is selected. The field characteristic is not constrained beyond
the fixed field in `P`.

For duplicate-notion searches I reran `rg` over Mathlib, the upstream
`WeilConjectures` tree, and shared `lean/Sheaf`, plus the prescribed LeanFinder and
Loogle searches for normal cone, normal bundle, conormal algebra, and regular pure
codimension. The upstream cone candidate is `Scheme.Hom.NormalConeData`, whose source TODO
explicitly says it is not tied to the immersion; it carries only a smooth projection
with a closed section; it therefore cannot serve this node. No exact Mathlib or project declaration
exists. The recorded ideal sheaf, ideal powers, tensor pullback, locally-free, relative
Spec, and vector-bundle declarations were read and match their dependency statements.

The two dependency modules were independently checked as well. For
`lem-pur-conormal-graded-algebra`, `powerIdentification` matches the recorded ideal powers;
`piece` and `pushforwardPiece` give the tensor-pullback/sheaf-cokernel descriptions;
`coproduct`, `multiplication`, and `constants` give the graded algebra and its unit;
`affineChart` and the representative formulas determine the affine graded charts and
restriction compatibility; `quotientStalk`, `conormalStalk`, and `stalkChart` give all three
stalk clauses; `symmetricComparison` and `symmetricStalk` give the canonical map, its
values on scalar germs, and its value on degree-one germs; `coherent` has exactly the
locally Noetherian hypothesis and
only asserts coherence of individual degrees. For `def-pur-regular-immersion`, the body
of `IsRegularImmersionOfPureCodimension` is exactly `1 ≤ c`, the stated Krull-dimension
identity at each `z`, and a length-`c` regular generating sequence for the stalk kernel.
The source's smooth-pair parenthesis is a forward theorem pointer and adds no hypothesis.
There are no new definition nodes in this delivery.

The current shared conormal node acquired its ten-step split after the sandbox copy was
made. I retained its current metadata (only the supplied `lean` record differs from the
base) and checked the module against that proof plan. I found missing proof-dependency
imports in the conormal and normal-bundle modules and added them as ordinary `import`
lines, including the closed-pushforward, affine-pullback, stalk/direct-sum,
symmetric-base-change, and coherence tools. The main item
signatures and definition bodies, the node statements, and the dependency lists are
unchanged. All three modules are validated by the
required `scompile.py`/`deliver2.py` wrappers; every postponed proof remains `sorry`.

I also found that `Presentation.symmetricStalk` originally pinned only the images of
linear generators. That does not by itself fix the scalar ring: when the conormal stalk
is zero the symmetric algebra is the scalar ring and has no nonzero linear generators.
I added the scalar-germ formula to this field, alongside the existing generator formula,
and documented it in the existence theorem's proof. I also expanded that docstring
to follow the current node's ten proof steps explicitly. This explicitly makes the chart the
canonical algebra identification demanded by the dependency node. The existence theorem's
recorded signature remains verbatim the same, since it quantifies over `Presentation i`.

Independent search log: LeanFinder query "Relative spectrum of the graded ideal
quotients for an immersion; regular sequences make its conormal module locally free"
returned eight Proj and closed-subscheme construction hits, none an exact match. Loogle
`"normalBundle"` and msearch grep `normal.?cone|conormal.?algebra|normal.?bundle` in
Mathlib AlgebraicGeometry returned zero hits. The separate upstream/project `rg` searches
found and ruled out the unrelated `NormalConeData` interface after reading its definition.
LeanSearch was retried for the relative spectrum and augmentation statement; the service
returned Internal Server Error, so no absence inference was drawn from it.

## Dependency modules

`lem-pur-conormal-graded-algebra`: its record had no Lean declaration or Mathlib match.
The delivery supplies `Sheaf.AlgebraicGeometry.ConormalGradedAlgebra`, containing the actual
fixed homogeneous tensor-pullback modules, the complete universally characterized algebra
interface, affine and stalk class identifications, degree-zero and degree-one descriptions,
coherence, symmetric comparison and augmentation. Its existence theorem has a complete
source-based proof docstring. Only the node's lean field is supplied.

`def-pur-regular-immersion`: its record had no Lean declaration or Mathlib match. The delivery
supplies `Sheaf.AlgebraicGeometry.RegularImmersionPureCodimension`, rendering the positive
codimension, stalkwise dimension equality and regular-sequence generator clauses exactly
in separated finite-type schemes over the field. This retains the chapter's convention
without using the unsuitable upstream NormalConeData. Only the node's lean field changes.

Validation: the prescribed scompile wrapper compiled the dependency modules cleanly, and
`deliver2.py Q04 def-pur-normal-bundle --no-push` printed OK for compilation and preflight,
with only the expected independent second reading outstanding. No delivery was pushed.
The final stable files are checked again by the same dry-run wrapper after adding the
explicit inclusion-preserving identification with the recorded ideal-sheaf powers.


### Immutable maintainer review correction (2026-10-16)

The independent maintainer reader replaced the inline `by simp` in
`PurityNormalBundle.augmentationToBase` with the existing categorical identity theorem
`Category.id_comp _`. This changes neither the definition's data nor any declaration
signature; all postponed mathematical proofs remain `sorry`. The identity-immersion
edge-case discussion above is corrected to distinguish a nonempty base from the empty
base. The empty identity does satisfy the positive-codimension predicate vacuously.
The complete replacement module and this complete replacement report are supplied in
the review fixes directory; the node records require no change.

Maintainer validation: `scompile.py Q04 def-pur-normal-bundle` returned exit 0
with no compiler diagnostics for the replacement normal-bundle module together with
the two immutable dependency modules. All three files passed their separate sandbox
and library checks using the local side overlay, with the default per-file limits.
The original three immutable files were also independently compiled successfully.
