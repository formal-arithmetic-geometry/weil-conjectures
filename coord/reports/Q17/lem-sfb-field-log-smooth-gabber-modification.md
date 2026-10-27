## Worker report

The module `Sheaf.AlgebraicGeometry.FieldLogSmoothGabberModification` states
`AlgebraicGeometry.exists_field_logSmooth_gabber_modification`, with one postponed
proof and no new definitions. The informal statement and proof are unchanged.
Four already-landed definition nodes are added to `stmt_deps` for the precise
interfaces used: `def-per-fs-log-group-action`, `def-per-gabber-modification-data`,
`def-per-divisorial-log-cover-boundary`, and `def-sc-quasi-projective`.

Read the item's full statement, source and seven proof steps; every original
statement dependency's statement and recorded declaration; the relevant full
source signatures and docstrings; the four added nodes and the definitions used
from their modules. Read ILO X Theorem 1.1 and Remark 1.1.1, printed pp.135--136,
and the retained-boundary chart argument in X 1.8, pp.146--148. The current
blueprint is `literature/blueprint/latest/`; the relevant unit proof is
`sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
clause (3). This item is a generic geometric input below the unit, rather than a
unit-level theorem.

Hypotheses, clause by clause:

- The arbitrary field is `(F : Type u) [Field F]`. There is no perfectness or
  characteristic restriction beyond the stated group-order condition.
- The trivial log field is presented by `N : EtaleLogStructure (Spec (.of F))`,
  `hN : N.IsFineSaturated`, and `htrivial : N.trivialityLocus = Set.univ`.
  This is a presentation of the prescribed trivial log structure: the log unit
  condition identifies a log structure with everywhere-zero characteristic with
  the units, through its structural map. This is the same convention already
  used by `IsFreeCharacteristicLogSmoothDivisorialPair`; it introduces no
  arbitrary base map or alternative structure.
- `X : FineSaturatedLogScheme.{u}` supplies the scheme, its locally Noetherian
  certificate, and a genuine fs log structure. `[IsIntegral X.scheme]` is
  integrality, including nonemptiness.
- `f : EtaleLogHom X ⟨Spec (.of F), inferInstance, N, hN⟩` is the actual structural
  log morphism. Its underlying morphism has `[LocallyOfFiniteType f.base]` and
  `[QuasiCompact f.base]`, exactly finite type in the recorded convention, and
  `hprojective : IsQuasiProjective f.base`, exactly a locally closed immersion
  over F into finite-dimensional projective space.
- The closed subset B is represented without a choice of scheme structure by
  its open complement `U : X.scheme.Opens`. `hdense : Dense (U : Set X.scheme)`
  says its complement is nowhere dense. Every closed subset with dense complement
  is represented this way.
- `hdivisorial : X.logStructure.IsDivisorialFor U` identifies the log presheaf
  with `divisorialLogPresheaf U.ι`, commuting with `divisorialStructuralMap U.ι`.
  Thus the log sheaf is the specified regular functions invertible on U, rather
  than a different structure with only the same support. `hboundary` identifies
  its triviality locus exactly with U, and `hregular : X.IsLogRegular` is the
  strict-local regularity and Krull-dimension formula. The fs certificate is in X.
  These use the divisorial construction from the recorded LogRegularPair module
  and the general log regularity interface from FineSaturatedLogBlowup.
- `hsmooth : f.IsLogSmooth` uses the existing compatible fs chart criterion.
- `(G : Type v) [Group G] [Finite G]` and
  `horder : IsUnit (Nat.card G : F)` are the finite group of invertible order.
  `a : FSLogGroupAction G X` is an action by actual log automorphisms, hence
  preserves the triviality locus and the pair. `hover` says each underlying
  automorphism is over F. Because the base log structure is the units, its log
  section maps are forced by the regular-function compatibility; the scheme
  equation is therefore also the required trivial-base log equivariance.
- `hfree : a.IsGenericallyFree` is freeness on geometric points of a dense
  invariant open. `GabberModification.freeLocus a` is the union of all invariant
  free opens, so its complement is exactly the T in the statement. It is not
  replaced by one chosen smaller free open.

Conclusions, clause by clause:

- Existential Y is an fs log scheme, and `IsIntegral Y.scheme`,
  `LocallyOfFiniteType g.base`, `QuasiCompact g.base`, and
  `IsQuasiProjective g.base` give precisely integral quasi-projective finite type
  over the same F. The structural morphism is `g`, into the exact same bundled
  log field as f.
- `h : EtaleLogHom Y X`, `IsHProjective h.base`, `b.IsEquivariant a h`, and
  `h.CompEq f g` give the G-equivariant H-projective morphism over F. In
  particular both underlying scheme maps and log section maps commute.
- The existential dense opens `V₀`, `W₀`, their isomorphism `e`, and
  `e.hom ≫ W₀.ι = V₀.ι ≫ h.base` express birationality of this particular h,
  exactly in the stated dense-open sense. They do not merely assert the two
  schemes admit an unrelated birational identification.
- The equality for the output open V is
  `V = h.base ⁻¹' (U ∩ GabberModification.freeLocus a)` on underlying sets.
  Taking complements is exactly B' = h⁻¹(B union T), with no extra boundary.
  The existential open V also asserts that this complement is open, hence B'
  is closed; no scheme structure on B' is imposed.
- `Y.logStructure.IsDivisorialFor V`, its triviality equality, `Y.IsLogRegular`
  and `g.IsLogSmooth` give every modified-pair clause. Fine saturation is in Y.
- `b.IsVeryTame` is exactly the recorded three-part definition: invertible
  inertia order, trivial characteristic-monoid action, and identity on the
  strict-local stratum quotient, tested on all pointed relative etale germs.
- `P`, `q : EtaleLogHom Y P`, `IsFinite q.base`, `Surjective q.base`, and
  `b.IsQuotient q` give the categorical geometric scheme quotient, invariant
  structure sheaf and invariant direct-image log sheaf. The latter predicate
  includes the actual canonical section maps, injectivity and exact invariant
  images; an arbitrary independent log structure is not substituted.
- The separate universally quantified equation for geometric points y,z says
  `y ≫ q.base = z ≫ q.base` iff `z = y ≫ (b.baseAction k).hom` for some k.
  This explicitly retains orbit geometric fibres, in addition to the ordinary
  topological orbit condition already in `IsQuotient`.
- `IsIntegral P.scheme`, the finite-type conjunction for r, and
  `IsQuasiProjective r.base` give the asserted quotient geometry over F.
  `q.CompEq r g` makes the quotient's log structural map the descended map to
  the same fixed field, not a morphism to a changed base.
- The open W is exactly `(q.base '' (V : Set Y.scheme)ᶜ)ᶜ`, i.e. the complement
  of p(B'). `P.logStructure.IsDivisorialFor W` identifies the already invariant
  quotient log structure with this precise divisorial structure; its triviality
  equality, fs certificate, `P.IsLogRegular` and `r.IsLogSmooth` give all the
  remaining quotient clauses. Existence of W includes closedness of p(B').

Dependency declarations and modules:

- `Field`: Mathlib.Algebra.Field.Defs.
- `IsIntegral`: Mathlib.AlgebraicGeometry.Properties.
- `LocallyOfFiniteType`, `QuasiCompact`:
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact.
- `IsHProjective`: WeilConjectures.AlgebraicGeometry.Morphisms.Projective,
  the upstream declaration recorded on def-kun-projective.
- `divisorialLogPresheaf`, `divisorialStructuralMap`:
  Sheaf.AlgebraicGeometry.LogRegularPair. These occur through the existing
  `EtaleLogStructure.IsDivisorialFor` in DivisorialLogCoverBoundary, added via
  its already-landed node; no second divisorial definition is written.
- `FineSaturatedLogScheme`, `EtaleLogStructure.trivialityLocus`,
  `FineSaturatedLogScheme.IsLogRegular`, `EtaleLogHom`, `EtaleLogHom.CompEq`:
  Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup.
- `EtaleLogHom.IsLogSmooth`: Sheaf.AlgebraicGeometry.FSLogSmoothEtale.
- `FSLogGroupAction.IsVeryTame`: Sheaf.AlgebraicGeometry.VeryTameFSLogAction.
- `IsFinite`, `Surjective`: Mathlib.AlgebraicGeometry.Morphisms.Finite and
  UnderlyingMap.
- `FSLogGroupAction`, `IsGenericallyFree`, `IsEquivariant`, `IsQuotient`:
  Sheaf.AlgebraicGeometry.FSLogGroupAction (added already-landed stmt_dep).
- `GabberModification.freeLocus`: Sheaf.AlgebraicGeometry.GabberModificationData
  (added already-landed stmt_dep).
- `IsQuasiProjective`: WeilConjectures.AlgebraicGeometry.ProjectiveSpace.QuasiProjective
  (added already-recorded stmt_dep def-sc-quasi-projective). The general scheme
  declaration is the exact field-relative notion used here, despite its owning
  informal node discussing curves.

The file privately imports all available modules of recorded proof dependencies:
FieldsExcellent, ProjectiveBundleSeparated, GabberAbsoluteEquivariantModification,
VeryTameLogQuotient, GabberAbelianStageToricChart, LogRegularDivisorialStructure.
Two recorded proof-only modules, LogSmoothCompositionStrictBaseChange and
GabberFixedLocusLogChart, were explicitly deleted on 2026-10-20. They are absent
locally and `scompile.py --source` reports `Module source unavailable` for each.
They cannot be imported; their seven-step proof roles remain fully documented in
the theorem docstring. The other two proof dependencies
lem-per-quasi-excellent-finite-type-stability and
lem-per-projective-finite-group-quotient have no recorded Lean module. No missing
statement prerequisite, interface repair, or new definition node is needed.

Edge cases checked before writing:

- B empty means U = top, so V is exactly the inverse image of the largest free
  open. No nonempty-divisor assumption appears in the divisorial predicates.
- G trivial is permitted: its order is 1, the largest free open is top, and the
  identity modification with the original boundary and quotient meets the clauses.
- A free action permits T empty; the formulas keep the original boundary exactly.
- The integral source is nonempty, exactly as required; a dense complement cannot
  be empty. No artificial empty-source case was added or excluded.
- F may be imperfect, of characteristic zero, or positive characteristic prime to
  the group order. Neither regularity of Y as an ordinary scheme nor an SNC
  resolution is asserted; those would go beyond this logarithmic theorem.
- Scheme and coefficient field share the standard scheme universe u; G has its
  independent universe v. Geometric point fields use the established Type u
  convention for Scheme.{u}. No site-universe equality was imposed.
- Quasi-projective finite coordinate types may be empty in the upstream definition;
  their projective space is empty, so this cannot inadvertently admit a nonempty
  integral source with a spurious embedding. Finite dimension is otherwise arbitrary.
- The base log structure is actually fixed by the everywhere-trivial condition,
  and all g and r targets use the same N and hN as f.

Searches for an existing theorem/notion:

- msearch.py leanfinder: "Gabber log smooth modification of a scheme over a field
  with finite tame group action and log smooth quotient". Eight hits, led by
  AlgebraicGeometry.IsSmooth, IsSmooth.exists_isStandardSmooth, Scheme.Etale and
  IsSmoothOfRelativeDimension; none is this modification theorem.
- msearch.py loogle: `"log", "smooth"`. Twelve Diffeology smoothness hits;
  none is logarithmic algebraic geometry or Gabber's theorem.
- msearch.py grep, AlgebraicGeometry:
  `logSmooth|log_smooth|veryTame|very_tame|Gabber.*[Mm]odification`.
  Zero Mathlib hits.
- rg in WeilConjectures and Sheaf for the item id and field-log-smooth/Gabber
  declaration variants: no existing statement. The required explicit grep of
  the item id in WeilConjectures also found none.
- rg in the project for `IsQuasiProjective`, `FreeOpen`, `freeLocus`,
  `IsDivisorialFor`, `IsGenericallyFree`, `IsQuotient`, and trivial-log-field
  conventions found the exact reusable declarations listed above. The upstream
  name index also records IsQuasiProjective. These were used instead of copies.
- rg for birational definitions in Mathlib, WeilConjectures and Sheaf found
  scheme-to-scheme Birational/BirationalOver, not the specified-map condition
  here. The dense-open isomorphism with the commuting h equation follows the
  existing statement style of BirationalCommonDenseOpens and introduces no
  second named birational predicate.

No statement correction or STATEMENT-DISPUTED issue was found. Every variable
and universe is explicitly bound, autoImplicit is disabled, all lines have at
most 100 characters, and the only postponed proof is the item's named theorem.

Validation: scompile.py compiled the file on the server against the live library,
including the newly landed GabberAbelianStageToricChart overlay, with no errors
or unexpected warnings (the final module took 4.6 seconds).

## Second reading by Q17

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
