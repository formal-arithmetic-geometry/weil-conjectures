## Worker report

The item states Stacks Tag 08BC, lemma-existence-tricky, with Situation 08B7 and
Tag 08BA's ordinary component kernel/cokernel convention. The statement and proof
of these places in literature/stacks-project/spaces-more-morphisms.tex were read.
The only postponed theorem is
AlgebraicGeometry.AlgebraicSpace.coherentAdic_algebraization_of_bounded_exceptional_torsion.
Its proof is exactly `sorry`; its docstring carries all six DAG proof steps and their
uses. None of the three added support definitions contains postponed data or a proof obligation.

Hypotheses and conclusions, clause by clause:

- `universe u`, `S : Scheme.{u}`, and `X : AlgebraicSpace S` retain the base scheme,
  the recorded fppf-sheaf algebraic spaces and their small etale module sites, without
  identifying distinct site object/morphism universes. Coefficients and schemes have
  the universe of the recorded algebraic-space framework.
- `A : Type u`, `[CommRing A]`, `[IsNoetherianRing A]`, `I : Ideal A`, and
  `[IsAdicComplete I A]` give precisely a commutative Noetherian base ring and the
  canonical completion isomorphism. The adic-completion source defines this as separated
  and complete, equivalently bijectivity of its canonical inverse-limit map.
- `aS : Spec (.of A) ⟶ S` is the specified map; `f : X ⟶ schemeSpace (Over.mk aS)`
  is the map to that scheme as an algebraic space over S. `hsep` and `hft` use the
  recorded separated and finite-type properties; they do not impose flatness.
- `J K : QuasiCoherentIdeal X` use the existing ideal subobjects. `hJ` says their
  section ideal J on every affine etale chart is the extension of I under the
  actual chart map to Spec A. The scalar map is `GammaSpecIso.inv` followed by
  `appTop` of `yoneda.preimage (T.obj.hom ≫ f.hom.hom)`. This specifies J = I O_X,
  rather than supplying a new arbitrary ideal. Quasi-coherent ideals are determined
  by these affine charts. Equality of ideal sections with the extended ideal is
  required only on affine charts, avoiding the false claim about global sections
  of a generated ideal on general nonaffine tests.
- For every `e : ℕ` with `1 ≤ e`, the two parts of `hthickenings` say completion on
  proper-support coherent modules annihilated by K^e is fully faithful and essentially
  surjective onto proper-support coherent J-adic systems annihilated by K^e.
  The first uses `Function.Bijective` on the actual completion-induced Hom map;
  the second quantifies over every target diagram, with a coherent proper-support
  module and an isomorphism of complete diagrams as witnesses. These are precisely
  the two equivalence conditions for full subcategories. Completion automatically
  preserves annihilation and proper support. This is the intrinsic expression of
  the equivalence on X_e^K from the node: the source proof's first paragraph explicitly
  identifies both categories on X_e with these full subcategories on X. It is not an
  assumption merely about abstract equivalence of unrelated categories. In particular
  the node's closed thickening and restricted ideal are represented through their
  canonical closed-pushforward dictionary, without selecting a new closed subspace.
- `M` with `hM : IsCoherentAdicSystem J M` is exactly an object of Coh(X,J).
  Using its underlying diagram avoids adding a separately supplied proof of X being
  Noetherian: that follows from the stated finite-type separated map over Noetherian A.
  The three defining object conditions are unchanged, and all arrows are the same
  natural transformations. `hMproper` is the closed-carrier condition at `op 0`,
  which denotes the first positive level, not an extra zeroth level.
- `H : CoherentProperSupportModules f` means site quasi-coherence, the recorded
  coherent scheme restrictions on every etale chart, and a finite-type quasi-coherent
  module on a closed carrier proper over Spec A, with its direct image isomorphic to H.
- `a` is a natural transformation M to the actual completion diagram of H.
  `ha : CoherentAdicKernelCokernelKilled K a` retains one positive exponent for
  every ordinary component kernel and cokernel. It is not a kernel in Coh(X,J),
  not an exponent varying with the level, and not an arbitrary componentwise map.
- The existential `F : CoherentProperSupportModules f` retains both coherence and
  proper support over A. `Nonempty (completion.obj F.obj ≅ M)` is the asserted
  isomorphism of complete inverse systems, including every transition.
- No additional flatness, properness of X, I-adic separatedness of X, or supplied
  Noetherian proof for X has been added.

Dependencies used and signatures read:

- Mathlib.AlgebraicGeometry.Scheme: Scheme, Scheme.Hom, Spec, Scheme.GammaSpecIso,
  and scheme-map appTop; Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion:
  IsClosedImmersion. Mathlib.RingTheory.Noetherian.Defs: IsNoetherianRing;
  Mathlib.RingTheory.AdicCompletion.Basic: IsAdicComplete.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicSpace, IsRepresentableWith,
  EtaleSite, etaleForget, structureSheaf and Modules. Its regular-function
  structure presheaf is definitionally chart global sections.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: QCoh and the recorded
  slice instances, using Mathlib's SheafOfModules.IsQuasicoherent. The ideal binder
  uses QuasiCoherentIdeal from AlgebraicSpaceQuasiCoherentIdeal, already publicly
  imported by the recorded adic dependency.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: moduleDirectImage,
  its chart-limit model and the tensor adjunction. Proper carriers use precisely
  this direct image; no substitute is chosen.
- Sheaf.AlgebraicGeometry.CoherentFiniteType and its public upstream
  WeilConjectures.AlgebraicGeometry.Coherent: RingedSpace.IsCoherent,
  SheafOfModules.IsQuasicoherent and IsFiniteType. Mathlib.AlgebraicGeometry.Noetherian:
  IsLocallyNoetherian. The chart coherence in the module is the one in the adic node.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: MapIsSeparated,
  MapIsFiniteType, MapIsProper, read with their chart and point-topology definitions.
- Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor: the closed-carrier proper-support
  convention. The repair's generalized support is its identical explicit carrier data.
- Sheaf.AlgebraicGeometry.SpaceCoherentAdicSystem: IsCoherentAdicSystem,
  coherentAdicCompletionDiagram, CoherentAdicKernelCokernelKilled and the original
  CoherentAdicHasProperSupport. The category, completion and bound are all reused.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceArtinRees: idealSectionImage, used in hJ.
- The two stated proof dependencies are imported privately:
  Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus and
  Mathlib.RingTheory.Finiteness.Nakayama. Other proof dependencies have no Lean
  binding at this read and are not imported as nonexistent modules.

Edge cases checked: the empty space, zero modules and the zero ring are allowed;
I=0 gives constant positive completion levels and I=top with completeness forces
A=0. K=0 makes all positive thickenings equal to X and the hypothesis includes the
claimed effectivity. K=top makes the supplied error bound force a to be an isomorphism,
so H itself is a model. All exponents e are positive; the bound uses its recorded
positive exponent, and indexing op n means n+1 throughout. Arrows and isomorphisms are
of diagrams, not disconnected termwise choices. No support condition is confused
with properness of the entire ambient X.

Searches actually run with msearch.py:

- LeanFinder: "Algebraization of coherent adic systems by bounded kernel cokernel
  torsion and completion equivalences on closed thickenings" returned eight completion
  and formally smooth ring results; none states the algebraic-space theorem.
- Loogle: "IsAdicComplete, AdicCompletion" returned twelve ring/module-completion
  declarations, not this theorem. Those confirm the canonical-completion encoding.
- LeanSearch: "Algebraization coherent adic system proper support equivalence closed
  thickenings bounded torsion kernel cokernel" returned eight ring/module completion
  and module cokernel declarations, not this theorem.
- Mathlib grep: "adic.*algebraiz|algebraiz.*adic|torsionControlled" returned zero hits.
- Direct rg in both lean/WeilConjectures and lean/Sheaf for torsion algebraization,
  adic torsion and the node id found scheme-only torsion-controlled algebraization
  declarations and the existing adic-system definitions, not the requested theorem.
  Direct rg for each newly introduced helper name in both roots and Mathlib had
  no match. The original support predicate and proper Quot carrier were read.
- DAG searches for completion equivalences found the current node, its adic-system
  dependency and related algebraization lemmas, not a separately recorded general-base
  proper-support interface. `tools/blueprint_refs.py search 'coherent proper support
  completion'` returned zero blueprint nodes. No new independent notion is introduced.

Both delivered modules compiled individually through scompile.py against the live
server build, including the sibling import, without errors or unexpected warnings.
The dependency module retains its two existing sorry theorems and adds definitions only;
the item introduces one sorry theorem.
No statement correction or statement dispute was needed.

## Dependency modules

`def-sfb-space-coherent-adic-system`: the existing module fully supplies the diagrams,
completion functor and bounded ordinary errors. Its support helper, however, fixes the
base scheme to Spec A and accepts only X over Spec A. The consumer has an arbitrary S
and a specified morphism of S-spaces to Spec A, so that helper cannot be applied to it.
SpaceCoherentAdicSystem retains its entire live source and appends
ModuleHasProperClosedCarrier, the full subcategory CoherentProperSupportModules,
and the generalized first-term predicate CoherentAdicHasProperSupportOver. These are
real carrier data and subcategory restrictions of the recorded notions, with no new
coherence predicate, quotient, map, theorem or choice. Specializing S=Spec A and the
identity base map gives exactly the previous support condition by unfolding.
Only this dependency node's lean record changes; it retains the live module, primary
declaration CoherentAdicSystem and signature, and all 14 live declaration names, followed
by the three new support definitions. Its earlier interface remains public.

## Repair of the returned delivery

H13/H2: compared the returned sandbox with the live dependency record and read
SpaceCoherentAdicSystem from the server with scompile.py --source. The returned record
listed only three support definitions and made CoherentAdicHasProperSupportOver primary,
so it omitted the actual adic-system category, completion and bounded-error declarations.
The repair follows the maintainer's first proposed remedy: append the three definitions
to the live SpaceCoherentAdicSystem module, remove SpaceCoherentAdicProperSupport from
the sandbox delivery, and import SpaceCoherentAdicSystem directly in the item. The
dependency record retains its live module, declaration CoherentAdicSystem, original
statement, and all 14 live declaration names, and appends all three new names. The
source preceding the appended definitions is byte-for-byte the current server source
except for the placement of its final namespace closure. No existing declaration,
proof, or signature changes. The item's reviewed mathematical statement remains exact;
only its dependency import changes. The optional predicate refactoring is unnecessary
for this record repair. The definitions and their docstrings remain those read and
approved by the maintainer. Compilation and dry-run validation are repeated for this
repaired packet before delivery.

## Second reading by Q72

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
