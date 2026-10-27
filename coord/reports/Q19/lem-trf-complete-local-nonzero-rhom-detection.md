## Worker report

This repairs H3 in the return of immutable head `6f5874e84acd`.
The module `Sheaf.Algebra.Homology.CompleteLocalNonzeroRHomDetection` states
`DerivedCategory.complete_local_nonzero_rhom_detection`, with proof `sorry`.
The previous ModuleCat presentation did not supply an RHom-compatible comparison
with the one-object ringed-site presentation required by the node and its citer.
The repaired statement uses that ringed-site presentation directly.

The retained sandbox node was compared with the current read-only repository node:
only its `lean` field differed before this repair. The node is refreshed from that
base, with the repaired `lean` record and the expressly requested addition of
`def-pc-ring-hom-extension-shared-definitions` to `stmt_deps`. No mathematical
statement, proof step, proof dependency, source or other field is changed.
No new module for a dependency or new definition node is necessary.

Each hypothesis and clause matches the node as follows:

- `(R : Type u) [CommRing R]` introduces its arbitrary commutative ring.
- `[IsNoetherianRing R]` is the recorded declaration of
  `def-weil-pbc-noetherian-ring` in `Mathlib.RingTheory.Noetherian.Defs`.
  `isNoetherianRing_iff_ideal_fg` identifies it with finite generation of every ideal.
- `[IsLocalRing R]` includes `Nontrivial R` and has unique proper maximal ideal
  `IsLocalRing.maximalIdeal R`, by `IsLocalRing.isMaximal_iff`.
- `[IsAdicComplete (IsLocalRing.maximalIdeal R) R]` includes separatedness and
  precompleteness. `AdicCompletion.of_bijective_iff` identifies this with bijectivity
  of the canonical map to the inverse limit. Its n=0 quotient is zero and imposes
  no extra condition compared with the node's n>=1 indexing.
- `[HasDerivedCategory.{u} (RingSiteModules R)]` fixes the localization size,
  exactly as in the coherent-duality sibling and semidualizing citer.
  `DerivedCategory` is the recorded definition in
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, from
  `def-weil-abstract-derived-category`.
- `(C Z : DerivedCategory (RingSiteModules R))` realizes D(R) on the one-object
  category with bottom topology and constant ring sheaf, precisely the node's
  specified realization. `CategoryTheory.RingSiteModules`, from
  `Sheaf.Algebra.Homology.RingHomExtensionDefs`, is reused via the newly cited
  `def-pc-ring-hom-extension-shared-definitions`. Its full definition was read.
  It uses the existing `CochainComplex.onePointRingSheaf R` and sheaf module category;
  no equivalence with ModuleCat or arbitrary comparison is assumed.
- `hCfin` says `∀ i : ℤ, Module.Finite R
  (((homologyFunctor (RingSiteModules R) i).obj C).val.obj (op ⟨PUnit.unit⟩))`.
  `hZfin` states the same condition for Z. Evaluation at the unique site object
  yields the actual R-module whose finite generation the node requires.
  `Module.Finite` is the recorded notion of `def-weil-finitely-generated-module`;
  its definition in `Mathlib.RingTheory.Finiteness.Defs` says the top submodule
  has a finite spanning set. `homologyFunctor` is the cohomology functor induced
  through localization, from `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `hCbdd` and `hZbdd` separately assert existence of integers a,b and categorical
  vanishing of cohomology for `i < a ∨ b < i`, exactly a finite cohomological interval.
  Representatives and RHom need not be bounded.
- `hC : ¬ IsZero C` is precisely C nonzero. There is no nonzero hypothesis on Z.
- `hHom` uses `(derivedInternalHomOfUniverses.{u,u,u,u}
  ⊥ (CochainComplex.onePointRingSheaf R)).obj (op C,Z)`.
  This is `CategoryTheory.derivedInternalHomOfUniverses` from
  `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`, already listed in the
  `def-pur-derived-internal-hom` record. Its full signature, construction and
  representative-comparison docstrings were read: it is the Hom-complex localization
  using canonical functorial K-injective replacement in the second variable.
  It retains R-scalars and is contravariant in C and covariant in Z.
- `IsZero` of that object is RHom_R(C,Z)=0. The conclusion `IsZero Z` is exactly Z=0.
- No scalar-action, finite projective dimension, finite injective dimension,
  perfectness or extra monoidal structure on C is a hypothesis.

All variables and universes are bound, with `set_option autoImplicit false`.
All five statement dependencies and the three additional proof-dependency modules
are imported. The four proof steps and their source references remain in the docstring.
The source read is `dualizing.tex`, Tags 0BFR(2), lemma-ubiquity-dualizing, and
0A7C, lemma-dualizing, including unbounded coherent biduality; and `more-algebra.tex`,
Tags 0A65, lemma-internal-hom, and 0DJE, lemma-tensor-pseudo-coherent.

Edge cases: Z=0 is allowed; C=0 would make detection false and is expressly excluded.
An interval a>b forces all cohomology zero and does not rule out the zero target.
Fields with m=0 and arbitrary shifts are covered. Over k[e]/(e^2), C=Z=k is covered
without requiring finite projective dimension or bounded RHom. Localness is essential:
the complementary summands over k x k have zero mutual RHom. The zero ring has no
proper maximal ideal and is correctly excluded. The arbitrary universe u and the
one-object site, coefficient, module and chosen derived hom universes agree with
both the coherent-duality dependency and the sole citer.

Searches performed using the prescribed `msearch.py` wrapper:

- LeanFinder: "Derived Hom from any nonzero bounded coherent complex over a complete
  Noetherian local ring detects zero bounded coherent complexes". Eight hits;
  `DerivedCategory.to_singleFunctor_obj_eq_zero_of_injective`, `isLE_iff`, `IsLE`,
  `isGE_iff` and related cohomological-bound results. None states this detection theorem.
- LeanSearch: "Derived Hom from a nonzero bounded coherent complex over a complete
  local ring detects zero". Eight hits; Hom-complex zero classes, the derived zero
  object, localization and Ext size results. No matching detection theorem.
- Loogle: `DerivedCategory, "isZero"`. Four hits: `isZero_of_isGE`, `isZero_of_isLE`
  and their Plus analogues. These concern bounds in a single degree, not RHom detection.
- Mathlib grep: `dualizing|RHom.*(nonzero|[Zz]ero)|complete.*local.*[Hh]om`
  in Algebra/Homology. Two unrelated hits in HomotopyFiber and Bifunctor.
- `rg` in the project's `lean/WeilConjectures` and `lean/Sheaf` for
  `nonzero.*rhom|rhom.*detect|complete_local.*[Hh]om|complete_local_nonzero`
  found no existing detection theorem. The required literal item-id grep in
  `lean/WeilConjectures` also found nothing. A further search for
  `ordinaryModuleDerivedInternalHom` found the existing dependency abbreviation
  and its relative-duality consumers. That interface is not used in this repair.

Validation: the repaired file passed scompile.py in both sandbox and library modes
(2.4 seconds each), with no errors or unexpected warnings. An optional temporary consumer
elaboration check stalled without returning a compiler result and was stopped; it
is not claimed as a passing validation and is removed from the delivered file.
Compatibility was checked by reading the actual definitions as detailed below.
The final file passed the delivery dry run, including server preflight and compile.
No STATEMENT-DISPUTED issue or mathematical statement correction is needed.

## Repair of returned delivery

H3 is repaired by replacing DerivedCategory (ModuleCat R) with
DerivedCategory (RingSiteModules R), adding its explicit HasDerivedCategory binder,
evaluating finite-generation conditions at the unique site object, and replacing
the closed-monoidal ordinaryModuleDerivedInternalHom with the recorded
`derivedInternalHomOfUniverses.{u,u,u,u}` on the one-object ringed site.
The requested existing shared-definition dependency is added, and imports,
module/declaration docstrings, verbatim lean.statement and this report are updated.
The direct derivedInternalHomOfUniverses option in the return was chosen, so no
additional SignedRingedHom statement dependency is necessary.

Consumer compatibility: `lem-trf-semidualizing-rhom-conservative` has the same
DerivedCategory (RingSiteModules R) endpoint and unique-object finiteness conditions.
Its SignedRingedHom.hom is a fixed-source composite of SignedRingedHom.homFunctor;
the latter is defined as exactly derivedInternalHomOfUniverses.{u,u,u,u}.
These definitions were read in RingedInternalHomSignedCalculus.lean. Thus its
RHom-zero hypothesis is definitionally the antecedent of the repaired theorem,
without an RHom comparison theorem, a chosen equivalence or any change of category.
The complete-local-coherent-duality dependency likewise uses RingSiteModules R.
No downstream file is edited.

## Second reading by Q19

I separately reread the repaired signature against the node and the sole citer.
The dispatcher's prohibition on starting other agents means this is a self-check;
the maintainer supplies independent review. The category and Hom mismatch recorded
as H3 is corrected: both C and Z now belong to the specified one-object ringed-site
D(R), their finite cohomology modules are evaluated at its unique object, and the
RHom expression is the very implementation used by the citer's SignedRingedHom.hom.
The complete-local ring hypotheses, separate boundedness and finiteness clauses,
C nonzero, RHom zero and Z zero clauses all remain present. No dimension or
scalar-action hypothesis was introduced. The added localization binder follows
the siblings' universe convention. The node's new statement dependency names the
existing definition actually used. The recorded Lean signature is verbatim from
the final file, which retains a single theorem with only sorry as its proof.
