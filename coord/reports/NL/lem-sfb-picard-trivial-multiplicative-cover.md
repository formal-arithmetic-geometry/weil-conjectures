## Worker report

The delivery states `AlgebraicGeometry.picard_trivial_multiplicative_cover` in
`Sheaf.AlgebraicGeometry.PicardTrivialMultiplicativeCover`. Its only theorem has
`by sorry`; there are no definitions, auxiliary axioms, or proofs. The source is
Milne, Algebraic Groups (2017), Proposition 18.22, printed pp.392–393, with the
standing split hypothesis automatic over the algebraically closed field. I read
the local PDF (including Definition 18.1 and the split hypothesis preceding 18.15).
The docstring gives all five DAG proof steps, including finite iteration, the
explicit tautological-line trivialization, and the smooth connected lift correction.

Clause-by-clause rendering:

- An algebraically closed field F: `(F : Type u) [Field F] [IsAlgClosed F]`.
- An F-group scheme G: `(G : Over (Spec (.of F))) [GrpObj G]`; no commutativity
  of G is assumed.
- Affine and finite type: `[IsAffine G.left] [LocallyOfFiniteType G.hom]
  [QuasiCompact G.hom]`. Finite type is the recorded conjunction, not just its
  local part.
- Smooth and connected: `[Smooth G.hom] [ConnectedSpace G.left]`. ConnectedSpace
  includes nonemptiness, matching the node's convention.
- Existence of a group P over the same field: `∃ (P : Over (Spec (.of F)))
  (_ : GrpObj P), ...`. Its affine, finite-type, smooth, connected conditions are
  the five successive conjuncts `IsAffine P.left`, `LocallyOfFiniteType P.hom`,
  `QuasiCompact P.hom`, `Smooth P.hom`, and `ConnectedSpace P.left`.
- A homomorphism f:P→G: `∃ (f : P ⟶ G) (_ : IsMonHom f), ...`. The existential
  group and homomorphism structures scope over the kernel predicate.
- Faithfully flat F[G]→F[P]: `f.left.appTop.hom.FaithfullyFlat`. The reversal
  of direction is the existing scheme global-sections pullback. RingHom.FaithfullyFlat
  is faithful flatness of the target as a module over the source; equivalently,
  scalar extension is exact and detects zero modules.
- Scheme-theoretic kernel: `GrpObj.ker f`, the pullback of f along the identity
  section. This is not a kernel on F-valued points.
- Finite kernel: `IsFinite (GrpObj.ker f).hom`. Over a field this means its
  coordinate algebra is finite-dimensional, as stated by the recorded group-scheme
  conventions.
- Diagonalizable kernel: `IsFiniteDiagonalizableGroupScheme (GrpObj.ker f)`.
  This landed definition quantifies over finite abelian groups M and natural group
  isomorphisms on all F-test schemes with Hom(M,Γ(T,O_T)ˣ). Its documented equivalence
  to Spec F[M] has exactly the basis group-like comultiplication, counit and antipode
  in the node. Multiplicative notation for M is just additive notation renamed.
  The already landed definition node `def-sfb-finite-diagonalizable-group-scheme`
  was added to stmt_deps; no second predicate is introduced.
- Pic(P)=0: `Subsingleton P.left.Pic`. Scheme.Pic is the existing set of invertible
  module isomorphism classes. Its canonical CommGroup uses multiplication for tensor
  product and 1 for O_P; subsingleton means every class equals that identity, so this
  is precisely the additive triviality asserted by the node. No curve restriction,
  cohomological replacement, or ring Picard specialization is imposed.
- The trivial group is included: there is no positive dimension or nontriviality
  hypothesis on G, P, or M. The zero-character-group kernel D(0) is permitted.

Dependency declarations read and used:

- `def-weil-field`: Mathlib.Algebra.Field.Defs, `Field` (extends CommRing and
  DivisionRing, hence includes 0≠1).
- `def-weil-algebraic-closure`: Mathlib.FieldTheory.IsAlgClosed.Basic,
  `IsAlgClosed`; I also read the recorded AlgebraicClosure construction. Only
  algebraic closedness, not an extension or a chosen closure, occurs here.
- `def-sc-group-scheme`: Mathlib.CategoryTheory.Monoidal.Grp, `GrpObj`, and
  its recorded specialization in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs;
  `IsMonHom` and `GrpObj.ker` use its existing group-object interface.
- `def-weil-finite-type-morphism`: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  `LocallyOfFiniteType`, and Morphisms.QuasiCompact, `QuasiCompact`.
- `def-sbc-smooth-morphisms`: Mathlib.AlgebraicGeometry.Morphisms.Smooth, `Smooth`.
- `def-weil-connected-scheme`: Mathlib.Topology.Connected.Basic, `ConnectedSpace`.
- `def-pc-scheme`: Mathlib.AlgebraicGeometry.Scheme, `Scheme` and `Scheme.Hom`;
  Mathlib.AlgebraicGeometry.AffineScheme, `IsAffine`.
- `def-sc-gm-ga`: Sheaf.AlgebraicGeometry.StandardGroupSchemes,
  `StandardGroupSchemes.multiplicative` and its canonical Laurent Hopf group law,
  used in the characteristic-Picard proof dependency. The theorem itself needs no
  separate multiplicative-group object in its signature.
- Added landed dependency: Sheaf.AlgebraicGeometry.FiniteDiagonalizableGroupScheme,
  `AlgebraicGeometry.IsFiniteDiagonalizableGroupScheme`.
- Existing scheme Picard definition and tensor group law:
  WeilConjectures.AlgebraicGeometry.PicardFunctor, `Scheme.Pic`, and
  WeilConjectures.AlgebraicGeometry.Picard.Group, `Scheme.Pic.instCommGroup`.
- Faithful flatness: Mathlib.RingTheory.RingHom.FaithfullyFlat, `RingHom.FaithfullyFlat`.

Plain proof imports include the three recorded and stated proof prerequisites:
`Sheaf.AlgebraicGeometry.GroupScheme.BorelCharacteristicPicardSequence`
(`borel_characteristic_picard_sequence`),
`Sheaf.AlgebraicGeometry.MultiplicativeIsogenyComposition`
(`multiplicativeIsogeny_comp`), and
`Sheaf.AlgebraicGeometry.CharacterPicardIsogenySequence`
(`characterPicard_isogeny_sequence`). Their full signatures and docstrings were read.
The other three proof prerequisites (flag-effective-picard-generators,
flag-projective-linear-system, projective-representation-smooth-lift) have no Lean
record at this read; there is no module to import. They remain in the docstring and
unchanged proof_deps. No statement dependency is missing or unusable.

Edge cases checked before drafting: the trivial group and an empty list of Picard
generators use the identity map; finite character group M may be trivial. Positive
characteristic includes μ_p and nonreduced kernels, since the diagonalizable
predicate uses all test schemes, not geometric points. No separability, etaleness,
reductivity, or characteristic-zero restriction is present. Empty schemes are excluded
only by the node's connectedness condition. The arbitrary universe u simultaneously
sizes F and its schemes; the existing Picard set lives in Type (u+1), which the
Subsingleton conclusion accepts. The finite character group is allowed in Type u,
including finite models in every universe. Pic(P) is inhabited by O_P, so its
subsingleton condition does not permit a vacuous empty Picard group.

Searches made before writing:

- msearch.py leanfinder: “A smooth connected affine group scheme over an algebraically
  closed field has a multiplicative isogeny cover with trivial Picard group”. Eight
  unrelated hits (affine covers, abstract Galois categories, Hom limit material);
  no affine group-scheme Picard-cover theorem.
- msearch.py leansearch: “A smooth connected affine algebraic group over an
  algebraically closed field has a multiplicative isogeny cover with trivial Picard
  group”. Eight ring Picard hits, including CommRing.Pic.subsingleton_iff and local
  ring Picard triviality. None states this theorem about group schemes.
- msearch.py loogle: `"Picard", "GroupScheme"`: zero hits.
- msearch.py grep in Mathlib AlgebraicGeometry:
  `[Pp]icard.*[Ii]sogen|[Ii]sogen.*[Pp]icard|[Pp]icard.*[Gg]roupScheme`: zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for the same regexp: the character-Picard
  isogeny sequence and the stable-exponent consumer, no cover theorem. Searching the
  item id in WeilConjectures produced no occurrence. Searching candidate declaration
  names in both Lean roots and dag/lean_names_upstream.json produced no match.
- Broader rg searches for diagonalizable, Picard and multiplicative isogenies found
  the already landed finite-diagonalizable definition and composition theorem. Read
  those modules and the owning DAG node, and reused their existing definitions.

No statement correction or STATEMENT-DISPUTED issue was found. The signature preserves
all original hypotheses and conclusion clauses. Only lean and the addition of the
already landed definition to stmt_deps change in the copied node.

## Second reading by NL

The dispatcher explicitly forbids starting other agents and assigns the independent
review to the maintainer. This is a second self-reading, not a claimed independent
worker review. Reopened the original node and final module and checked the clause
mapping above: field/algebraic closedness; F-group structure; affine, both finite-type
conditions, smooth, connected assumptions on G; existential P with the same five
properties; group homomorphism; faithfully flat coordinate pullback; finite and
scheme-theoretically diagonalizable kernel; trivial existing scheme Picard group.
No extra hypothesis or conclusion was found. In particular neither G nor P is assumed
commutative, and the kernel is not assumed reduced. The Subsingleton conclusion
identifies every invertible class with the already existing structure-sheaf class.
No mathematical change was needed after this reading. Compiler and delivery validation
are recorded below.

Validation: scompile.py compiled the sandbox and final library module without errors
or unexpected warnings. deliver2.py --no-push returned
`OK (dry run): commit 1c6b045d16a passes the preflight and compiles; nothing pushed`.
The dry run staged exactly this module, this node copy, and this report.
