## Worker report

The module states general preservation of log regularity under chart-log-smooth
morphisms, log regularity of a trivially logged field, and its explicit application
to a log-smooth morphism over that field. All three named theorems have sorry proofs;
there are no new definitions and no statement correction.

Clause correspondence:

- The locally Noetherian fs log schemes are X Y : FineSaturatedLogScheme.{u}.
  Their bundled fields include locallyNoetherian and fineSaturated.
- The given log morphism is f : EtaleLogHom X Y, including its actual structural
  compatibility and maps on log sections.
- Chart log smoothness is hf : f.IsLogSmooth, using the recorded definition verbatim.
  Its finite kernel and invertible torsion conditions are retained; no injectivity
  or torsion-free-cokernel hypothesis is added.
- Base log regularity is hY : Y.IsLogRegular; the conclusion is X.IsLogRegular.
  This is exactly regularity of every geometric stratum quotient and the Krull
  dimension equality with the rational rank of the characteristic group.
- The arbitrary field is (F : Type u) [Field F], without perfection or characteristic
  restrictions. N is its fs log structure, and htriv : N.trivialityLocus = Set.univ
  specifies triviality everywhere using the existing definition, as in the landed
  FreeCharacteristicRelativeNCCriterion and LogCotangentCharacteristicQuotientTrivialBase.
  The log unit condition then identifies N with the trivial structure.
- isLogRegular_trivialLogField states the node's assertion that this base is log regular.
  The last theorem states the resulting preservation over it, without assuming base
  log regularity again. No existence claim is replaced by an arbitrary map or choice.

Statement dependency declarations read and used:

- Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup:
  AlgebraicGeometry.FineSaturatedLogScheme, EtaleLogHom,
  FineSaturatedLogScheme.IsLogRegular, EtaleLogStructure.trivialityLocus.
- Sheaf.AlgebraicGeometry.FSLogSmoothEtale:
  AlgebraicGeometry.EtaleLogHom.IsLogSmooth (via its actual FSLogChart.IsSmoothChart).
- Mathlib.Algebra.Field.Defs: Field (the def-weil-field Mathlib match).

Proof-dependency modules with existing records are imported privately, including
completion and strict-henselization inputs, the associated-log stalk interface,
face sharpening, sharp and completed charts, formal monoid ring dimension, and the
older torsion-free theorem. lem-sfb-completed-tame-monoid-base-change-model has no
recorded declaration yet and is not needed to type this statement; its import must
be added when that proof prerequisite is stated. Its mathematical use is retained
in the main theorem's complete proof docstring.

Edge cases checked before writing: the empty source gives vacuous pointwise log
regularity; the identity reduces to the same condition; trivial characteristic has
rank zero and zero log ideal; an imperfect field is regular of dimension zero;
positive-characteristic torsion is subject only to the existing invertibility
condition. Noninjective prescribed chart maps are allowed by IsLogSmooth, unlike
the older logSmooth_invertibleTorsion_logRegular declaration. Arbitrary chart ranks
are allowed. All type and universe variables are explicit; autoImplicit is false.

Searches actually run in this session:

- msearch leanfinder: "Log smooth morphisms of locally Noetherian fine saturated log
  schemes preserve log regularity": eight ordinary scheme smoothness hits, no log match.
- msearch loogle: '"LogSmooth", "LogRegular"': zero hits.
- msearch grep: 'IsLogRegular|IsLogSmooth|log_smooth.*log_regular': zero Mathlib hits.
- msearch leansearch: "Log smooth morphisms preserve log regularity": eight ordinary
  scheme/ring smoothness hits, no log match.
- rg of lean/WeilConjectures for IsLogRegular, log regularity/smoothness and this node
  id: no matching theorem. rg of lean/Sheaf found the existing definitions and the
  stronger chart hypotheses of LogSmoothLogRegular and
  LogSmoothInvertibleTorsionLogRegular; their signatures and docstrings were read.
  Neither is the general chart criterion of this item, and neither includes its
  arbitrary-field clause. The field class signature and docstring were also read.

Source checked directly with pdftotext on ILO PDF pages 75--76 (printed 69--70).
VI 1.1 supplies the locally Noetherian convention; VI 1.2 the log regularity
condition; VI 1.3 identifies trivial-log regularity with ordinary regularity;
VI 1.8 states the full preservation theorem and refers to Kato 1994 Theorem 8.2.
No mathematical dispute was found. The live reviewed field is a stage-1 review by
NO dated 2026-10-22, and reviewed_lean is absent: this is a new stage-2 statement,
not an attempt to redo the stage-1 split.

## Second reading by NG

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
