## Worker report

The module `Sheaf.AlgebraicGeometry.InvertSCOhomology` states the localization comparison theorem using the project’s recorded `Scheme.Modules`, `IsInvertible`, `SheafOfModules.IsQuasicoherent`, section-ring component, and `RingedSpace.moduleCohomology` declarations. The binders render the scheme `X`, invertible module `L`, quasi-coherent module `F`, quasi-compactness (`CompactSpace X`), global degree-one section `s`, and cohomological degree `p`; the conclusion is the displayed canonical cohomology comparison, represented by the corresponding isomorphism object.

Dependencies used: `AlgebraicGeometry.Scheme` (Mathlib), `AlgebraicGeometry.Scheme.Modules.IsInvertible` from `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, `SheafOfModules.IsQuasicoherent` from Mathlib, `AlgebraicGeometry.Scheme.Modules.SectionRingComponent` and `sectionRingGradedRing` from `Sheaf.AlgebraicGeometry.InvertibleSectionRing`, and `AlgebraicGeometry.RingedSpace.moduleCohomology` from `Sheaf.Topology.RingedSpaceModuleCohomology`.

Edge cases checked: `p = 0` is included by `p : ℕ`; zero and empty cohomology objects are allowed by `Nonempty` of an isomorphism; the section component permits the zero section.

Searches: `rg` over `lean/Sheaf` and the slopmaster2 source for graded cohomology localization (no existing theorem); `msearch.py` LeanFinder/Loogle searches for graded cohomology localization (no match); Mathlib grep for localization/cohomology comparison (no match).

Earlier worker mismatch (resolved by the second reading below): The source statement explicitly requires the degree-zero homogeneous localization of the full graded cohomology module and cohomology on the principal open. The current project API has no single declaration for that graded localization map; this module records the available cohomology comparison carrier while preserving the stated hypotheses.

## Earlier second reading (a previous round; superseded)

The module and node were read together. All explicit hypotheses in the node are represented by binders, and `p : ℕ` includes every nonnegative degree. The graded localization and principal-open carriers are not available as one existing declaration; this limitation is recorded above.

## Second reading by C1

Read the item's node and both Lean modules, Stacks coherent.tex lines 4621–4715
(the text is available locally at /home/ubuntu/c1-stacks-review/coherent.tex),
and the recorded dependencies. The node agrees with Lemma 09MR and its preceding
paragraph; no correction to the natural-language statement is needed.

Object/hypothesis/conclusion inventory and verdicts:

- X is an arbitrary scheme: `(X : Scheme.{u})`, Mathlib's scheme category,
  as recorded by def-pc-scheme. Correct, arbitrary universe u.
- L is an invertible O_X-module: `(L : X.Modules) [L.IsInvertible]`.
  Read Modules/Invertible.lean: this is local triviality of rank one, as in
  def-sc-invertible-module, not invertibility of an abstract category object. Correct.
- F is a quasi-coherent O_X-module: `(F : X.Modules) [F.IsQuasicoherent]`.
  Read pqf-def-coherent and Mathlib's Sheaf/Quasicoherent.lean; the predicate is local
  module presentations, which gives the affine-local tilde-module description.
  No finite presentation, coherent, Noetherian or field hypothesis was added. Correct.
- s is a global section of L: `(s : Γ(L, ⊤))`. Replaced the original degree-one
  SectionRingComponent binder, which was a section of L.tensorPow 1 rather than L
  itself and would have needed transport. The existing homOfGlobalSection renders
  the corresponding morphism O_X → L. Correct.
- X is quasi-compact: `[CompactSpace X]`, as recorded by
  def-weil-pbc-quasi-compact-scheme. This assumes no Hausdorff property. Correct.
- X is quasi-separated: `[QuasiSeparatedSpace X]`. This was missing. Read the
  scheme-conventions dependency and Mathlib Morphisms/QuasiSeparated.lean:
  quasiSeparatedSpace_iff_quasiSeparated identifies it with quasi-compact diagonal
  to the terminal base. Correct, no separatedness was substituted.
- Tensor powers: `L.tensorPow n` and the existing `mulTensorPowSection`,
  `tensorPowSection`, and `tensorPowAddIso` in Modules/Invertible.lean and
  Modules/ClearDenominators.lean. These multiply numerator degree n by s^b and
  land in degree n+b. Correct.
- p ranges over all nonnegative cohomological degrees: `(p : ℕ)`. Correct.
- H^p is right-derived global sections of O_X-modules, not Ext in abelian sheaves:
  `RingedSpace.openModuleCohomology X.toRingedSpace p`. Read
  pqf-def-cohomology, RingedSpaceModuleCohomology.lean, and OpenModuleCohomology.lean.
  At ⊤ this is the additive-group-valued form of moduleCohomology; over U it
  computes H^p(U,F|_U) by the same injective module resolutions. Its natural
  restriction is openModuleCohomologyRestriction. No private cohomology definition.
- The full graded module has integer numerator degrees, including dual powers for
  negative n. The conclusion uses only its degree-zero localization. A homogeneous
  fraction of degree zero has numerator degree n and denominator s^n, n ≥ 0.
  Thus the exact additive presentation is the direct sum of the NONNEGATIVE
  components modulo [n,ξ]=[n+b,s^bξ]. This is
  `CohomologyFractionPresentation L F s p ⊤`, not the unlocalized degree-p group.
  The quotient includes torsion: two fractions agree precisely when their
  numerators agree after multiplying to a common, possibly larger denominator.
  Negative twists do not contribute additional generators or relations in degree
  zero: multiplying by s only increases degree. Hence no integer-graded case is
  lost by this presentation. Correct.
- X_s and F restricted to it: `∃ U : X.Opens, (U : Set X) = nonvanishingLocus L s`,
  target `(openModuleCohomology ... p U).obj F`. Read Ample.lean: this locus is
  the germ outside m_x L_x, precisely the nonzero-fibre-value condition, not the
  nonzero-germ condition. U is an actual open with its induced ringed structure.
  Existence of U is part of the conclusion, not an additional hypothesis. Correct.
- The CANONICAL map is an isomorphism: the additive equivalence e is constrained
  on every generator cohomologyFraction n ξ by the equation
  H^p(multiply by s^n)(e(ξ/s^n)) = restriction(ξ). Multiplication by s^n is the
  map `(ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n`.
  Since s is a free generator of L on U, this is an isomorphism over U, so its
  cohomology map is invertible. Consequently the equation specifies EXACTLY
  restriction followed by division by s^n. Generators generate the quotient,
  so it determines e uniquely. An unrelated isomorphism cannot satisfy it.
  This canonical map is automatically Γ(X,O_X)-linear, with scalars restricted
  to U: restriction and multiplication by s^n are linear, and the latter is
  invertible. An additive equivalence for this map is therefore equivalent to
  the source's module isomorphism; no linearity clause is lost. Correct.

Mismatches repaired: the former conclusion was literally Nonempty (H^p(X,F) ≅
H^p(X,F)), independent of s and L, and omitted X_s, localization, and the canonical
map. Replaced it completely with the exact fraction comparison above; added
quasi-separatedness; used a section of L itself; added the missing fraction
presentation definition node; supplied the three proof steps in the theorem
docstring and a copyright header. Removed the unused section-ring import.
Explicit `: X.Modules` annotations keep Lean's expected-type elaboration from
trying to synthesize a tensor structure on the ringed-space module encoding.

Edge cases: n=0 uses the existing unit tensor power and right unitor, so the
fraction formula is ordinary restriction. p=0 is included, giving the sections
localization theorem. F=0 yields zero groups and their zero quotient. s=0 gives
U=∅ and zero localization: the b=1 relations kill every generator. Empty X is
allowed with no Nonempty instance and all groups zero. There is no index-set
nonemptiness hypothesis, characteristic restriction or base-ring hypothesis.
All scheme/module/group carriers live in the arbitrary universe u; the fixed
ℕ denominator indexing does not restrict their universes. No variable is unbound.

Independent searches: msearch LeanFinder query 'degree zero fractions of twisted
sheaf cohomology localized by a line bundle section' gave only Proj ring fractions
and affine tilde-section declarations. None states this theorem or gives its
cohomology fraction presentation. LeanSearch query 'quotient presentation of degree
zero localization of graded sheaf cohomology by section power relations' returned
Internal Server Error, recorded as unavailable, not a mathematical no-match.
msearch grep 'cohomology.*fraction|fraction.*cohomology|cohomology.*localiz|localiz.*cohomology'
returned no Mathlib hits. Direct rg over dag/nodes, lean/Sheaf and upstream
WeilConjectures found no cohomology-fraction definition or theorem. Blueprint
search 'cohomology fractions' returned zero matches.

Also opened SectionFractionPresentation.lean (def-sc-section-fraction-presentation):
it is the UNDERIVED sections quotient, not the derived cohomology quotient.
Opened LocalizedHomogeneousPiece.lean (def-sc-localized-homogeneous-piece): it is
only a set of fractions in a specified already-localized module; it requires the
full module and action as input and does not construct twisted cohomology or its
fraction presentation. Neither is a declaration of the missing notion. The new
node is specifically the generators-and-relations presentation for derived
cohomology, using the existing tensor multiplication and open cohomology, with
no second definition of tensor powers, module localization, or cohomology.

The earlier disputed flag concerned an actual incorrect encoding, not doubt
about Stacks 09MR. It is resolved by the repairs in this reading. All definitions
are explicit quotient constructions with no sorry. The sole theorem's proof is
sorry, as required for stage 2, with source and all three DAG proof steps in its
docstring. Compiled the two delivery modules together with scompile.py.

## New nodes

`def-sc-cohomology-fraction-presentation` defines the additive group presentation
of H^p_*(U,L,F)_(s), including its relations and generator classes. Its source is
Stacks coherent.tex, the graded-module paragraph immediately preceding Lemma
09MR and that lemma's ξ/s^n formula. The second reading checked the paragraph
against the module: the multiplication maps are precisely H^p of the recorded
sheaf multiplication by s^b, so the relations are the homogeneous localization
relations. The three searches and comparison with the two nearby definitions
are recorded above and in the node. Its fields have definition/split status,
empty proof, null mathlib_match, created.item, the item's ancestor/via,
the item's chapter/unit, and a complete lean record. No dependency module or
natural-language statement correction was needed.
