## Worker report

The module states `section_restriction_s_torsion` in the namespace
`AlgebraicGeometry.Scheme.Modules`. It binds a qcqs scheme (`CompactSpace X`,
`QuasiSeparatedSpace X`), invertible module `L`, quasi-coherent module `F`,
sections `s` and `t`, an open `X_s`, a vanishing restriction hypothesis, and a
family of multiplication maps into sections of `F ⊗ L^{⊗m}`; it concludes that
some power annihilates `t`. The tensor powers use the project's
`AlgebraicGeometry.Scheme.Modules.tensorPow` and tensor object.

Dependencies used: `AlgebraicGeometry.Scheme.Modules.IsInvertible` from
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`; Mathlib's
`AlgebraicGeometry.Scheme`, `CompactSpace`, `QuasiSeparatedSpace`, and
`SheafOfModules.IsQuasicoherent`.

The empty/zero cases are covered by `m = 0`; no nonemptiness assumption is made.
Searches with `msearch.py` (LeanFinder, Loogle, grep) found only structure-sheaf
lemmas `exists_of_res_zero_of_qcqs_of_top`, not the invertible-module statement.

## Earlier second reading (a previous round; superseded)

The declaration compiles with the stated imports and uses explicit universe and
instance binders. The conclusion quantifies a natural-number tensor power and
its section map. No dependency declaration is redefined.

## Second reading by F1

Read the node copy and the repository node against Stacks Properties Lemma
01PW, label `lemma-invert-s-sections`, especially the finite affine-cover
proof of part (1). The local source text is
`/home/ubuntu/c1-stacks-review/properties.tex`, lines 2226–2271; this machine's
repository literature checkout contains only the citation lists. The source
assumes a scheme, an invertible sheaf, and a quasi-coherent module. Injectivity
requires quasi-compactness; quasi-separatedness is required for the source's
second assertion and is explicitly present in this node. It remains in Lean,
so the statement exactly matches this node's specialization. The node itself
needs no correction.

Object/hypothesis/conclusion checklist (node's statement, Lean rendering, verdict):

- Scheme X: `{X : Scheme.{u}}`. Read Mathlib Scheme's `local_affine` field:
  a locally ringed space locally isomorphic to spectra, not a field-specific
  scheme. Matches `def-pc-scheme`.
- Quasi-compact X: `[CompactSpace X]`. Read `CompactSpace.isCompact_univ`;
  no Hausdorff hypothesis. Matches `def-weil-pbc-quasi-compact-scheme`.
- Quasi-separated X: `[QuasiSeparatedSpace X]`. Read Mathlib
  `quasiSeparated_iff_quasiSeparatedSpace` in Morphisms/QuasiSeparated. This
  agrees with the terminal-morphism definition in
  `def-weil-quasi-separated-morphism` and the affine-intersection description.
- Invertible O_X-module L: `(L F : X.Modules) [L.IsInvertible]`. Read the
  recorded source declaration in Modules/Invertible: `exists_isoUnit` gives
  local rank-one trivializations. This is the node's notion, and in particular
  implies quasi-coherence; no separate stronger hypothesis is introduced.
- Quasi-coherent O_X-module F: `[F.IsQuasicoherent]`. Read the dependency
  `pqf-def-coherent` and its module Coherent. Its module explicitly uses Mathlib
  `SheafOfModules.IsQuasicoherent` for this clause; its main recorded
  `RingedSpace.IsCoherent` is the coherent clause, which this item does not
  assume. Read Mathlib's local-presentation definition and Tilde's affine
  equivalence (`isQuasicoherent_iff_isIso_fromTildeΓ`). No finite-type,
  coherent, Noetherian, or separated assumption is imposed on F or X.
- Global section s of L: `(s : Γ(L, ⊤))`. Correct, actual global sections.
- Nonvanishing open X_s: `(X_s : X.Opens)` together with
  `(hXs : (X_s : Set X) = nonvanishingLocus L s)`. Corrected. Opened Ample's
  existing `nonvanishingLocus`, carried by `def-weil-pbc-ample-invertible-module`:
  the germ lies outside maximalIdeal times the stalk module. Read the
  residue-field dependency's `Scheme.residueField`: the quotient by the
  stalk's maximal ideal. Hence this condition says exactly that s has nonzero
  image in L_x tensor κ(x), since this tensor is L_x / m_x L_x. The equality
  merely names the open the node says to put X_s equal to; it is not an extra
  geometric assumption. Followed STATE's NON-VANISHING LOCUS convention.
- Global section t of F: `(t : Γ(F, ⊤))`. Correct.
- Restriction of t to X_s is zero: `hzero` uses `F.presheaf.map` on the
  opposite of the inclusion `X_s ≤ ⊤`. Correct, and now tied to s via hXs.
- Existence of a nonnegative exponent: `∃ m : ℕ`. Correct, includes zero.
- The image of t under multiplication by s tensor m is zero in sections of
  F tensor L tensor m: `tmulSection t (tensorPowSectionOne
  (homOfGlobalSection L s) m ⊤) = 0`. Corrected. Opened
  Modules/PullbackFreeGenerator's `homOfGlobalSection`, which sends 1 to s;
  Modules/ClearDenominators' recursive `tensorPowSection` (zeroth power the
  identity) and its evaluation-at-1 `tensorPowSectionOne`; and
  Modules/TensorSection's `tmulSection`, which sends the pure tensor to the
  sheafified tensor product. The result type is precisely
  `Γ(F ⊗ L.tensorPow m, ⊤)`, with the tensor product and powers defined in
  the recorded Invertible dependency. No arbitrary map remains.

Mismatches repaired: the original X_s was unconstrained and the original mul
was an arbitrary family of functions. For example, on Spec of a nonzero field,
choose L = F = O_X, X_s empty, and each mul the constant-one function: hzero
holds but the old conclusion fails. Added hXs and replaced mul with the
canonical tensor section. The original s did not occur in any condition or
conclusion; it now determines both. The original docstring lacked all three
proof steps; added the finite trivializing affine cover, the affine localization
kernel criterion, and the maximum exponent plus sheaf gluing, including their
DAG dependencies. Added the conventional license header and adjusted imports
for the existing canonical constructions. The earlier report's acceptance of
an arbitrary multiplication family is superseded by this reading.

Edge cases: no nonempty point set or cover is required. For empty X every
section is zero, and m = 0 works. For t = 0 or F = 0, m = 0 works by bilinearity.
For s = 0 the locus is empty and m = 1 annihilates every t; the earlier report's
claim that all empty/zero cases use m = 0 was inaccurate. For a nowhere-zero s,
hzero forces t = 0 and m = 0 works. The zeroth tensor power is O_X, and tensoring
with its section 1 is the unit isomorphism. There is no characteristic, base
field, finite-generation, or reducedness assumption. All objects live over
`Scheme.{u}` and its recorded `X.Modules`, with arbitrary bound u and no extra
independent test-object universe or hidden auto-implicit binder.

Independent searches (all msearch calls recorded in searches.jsonl):

- LeanFinder: `quasicoherent sheaf section zero locally on principal open killed
  by tensor power line bundle section`. Returned the structure-sheaf power
  annihilation lemmas in QuasiCompact/QuasiSeparated and tilde sections, not
  this general invertible-module statement.
- Loogle: `"exists_pow_smul_eq_zero"`. No hits.
- Mathlib grep: `exists.*(res.*zero|pow.*smul.*zero)|tensorPowSection` under
  AlgebraicGeometry. Eleven hits, all structure-sheaf cases or their uses.
- LeanSearch: `A section of a quasicoherent sheaf annihilated by some power of
  a line bundle section when zero on its nonvanishing open`. Service returned
  Internal Server Error; recorded as unavailable, not as negative evidence.
- Direct rg of source WeilConjectures and project lean/Sheaf, with
  `s_torsion`, `exists.*tensor.*zero`, `exists.*tmul.*zero`,
  `tensorPowSection.*= 0`, and `tmulSection.*= 0`: no equivalent statement.
  Opened the source ClearDenominators theorem: it is extension of sections
  from X_s and requires separation over an affine base, so it is not this
  assertion. Read GeneratingLocus's cokernel lemma: likewise another assertion.
  Searches of DAG and upstream-name records found the established auxiliary
  constructions, which are reused rather than duplicated.

No new definition node or dependency module is necessary: the required notions
already exist, and the dependency's quasi-coherent clause is explicitly Mathlib's.
No statement correction or citer verdict is needed. The only theorem proof is
`sorry`; no new definition, hollow data, or proved auxiliary lemma was added.
The module and declaration docstrings name 01PW and this item's blueprint id.
The node's lean.statement is extracted verbatim from the repaired signature.

Validation: scompile.py F1 lem-sc-p1-section-restriction-s-torsion on the repaired
SectionRestrictionSTorsion.lean compiled on the server in 2.3 seconds, exit 0,
with no warnings. Read the signature by eye: all universes, objects and variables
are bound, and all source hypotheses and conclusion clauses are accounted for.
