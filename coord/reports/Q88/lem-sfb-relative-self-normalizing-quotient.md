## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeSelfNormalizingQuotient` states
`AlgebraicGeometry.exists_relative_self_normalizing_quotient`. The only postponed
proof is this theorem, with the node's nine-step proof in its docstring. Four
explicit construction helpers belong to this same quotient statement: right
translation, the right-coset presheaf, its actual fppf sheafification, and the
canonical projection. They are listed in `lean.declarations`; their data contain
no sorry and no arbitrary choice of a quotient map.

Source checked: Conrad, *Reductive group schemes*, Theorem 2.3.6(1),(2), printed
pp.72--75, https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf . Theorem (1)
gives schematic smoothness under the self-normalizer hypothesis; theorem (2)
gives properness under projectivity of geometric quotient fibres. The opening
proof paragraph supplies local sections for smooth H. The node asks only for
these consequences, together with the functorial quotient and torsor identities,
not the additional quasi-projectivity, conjugate-subgroup moduli interpretation,
or canonical ample line bundle of the source theorem.

Hypothesis-by-hypothesis correspondence:

- Commutative ring A: `(A : Type u) [CommRing A]`, including the zero ring.
  The base is literally `Spec (.of A)`, not an arbitrary chosen affine scheme.
- Schemes over S and their group structures: `G H : Over (Spec (.of A))` and
  `[GrpObj G] [GrpObj H]`. This is the recorded group-object definition in the
  category of schemes over this base, with the usual multiplication, unit and
  inverse diagrams. It works over arbitrary A, not just a field.
- G affine over S: `[IsAffineHom G.hom]`; G smooth: `[Smooth G.hom]`.
  Finite presentation: `[LocallyOfFinitePresentation G.hom]` together with
  affineness, which supplies quasi-compactness and quasi-separatedness.
- Geometrically connected fibres of G: `[GeometricallyConnected G.hom]`.
  Mathlib defines this by connectedness after every field-valued base change;
  this is equivalent to the algebraic-closure test in the node. ConnectedSpace
  includes nonemptiness. Group identity sections also ensure nonempty fibres.
- Closed subgroup embedding: `(i : H ⟶ G) [IsMonHom i]` and
  `[IsClosedImmersion i.left]`. A closed immersion is a monomorphism; no
  separate and stronger rational-point injectivity assumption is imposed.
- Finitely presented embedding: `[LocallyOfFinitePresentation i.left]`;
  closed immersions are affine, hence quasi-compact and quasi-separated, so
  this says finite presentation rather than just locally finite presentation.
- H smooth with nonempty geometrically connected fibres:
  `[Smooth H.hom] [GeometricallyConnected H.hom]`. Nonemptiness is built into
  ConnectedSpace, including on the geometric fibres.
- Self-normalizing: `hself` quantifies over every S-scheme W and point g.
  Its antecedent tests equality of the conjugate image of H with H after EVERY
  map `a : V ⟶ W`; the two `Set.range` terms are the conjugate H(V) and H(V).
  This is equality of subgroup subfunctors over W, hence of the closed
  subschemes c_g(H_W) and H_W by Yoneda. Testing only H(W) would be incorrect.
  Its conclusion `∃ h : W ⟶ H, h ≫ i = g` is exactly g in H(W).

Clause-by-clause correspondence:

- The right-coset presheaf is `relativeSubgroupCosetPresheaf i t`: the
  coequalizer of the two actual transformations induced by `(g,h) ↦ g`
  and `(g,h) ↦ g i(h)`. Pointwise coequalizers of sets quotient by the
  generated relation, precisely the coset relation for a subgroup. No
  normality or commutativity of G or H is assumed. For `t = 𝟙 S` this is
  the presheaf of the node, canonically, and general t gives its base change.
- Q is `relativeSubgroupFppfQuotient i t`, defined by `presheafToSheaf`
  on the actual big fppf topology `(Scheme.fppfTopology.over T)`.
  Values use `Type (u+1)` and `uliftYoneda` so concrete sheafification exists
  at the site's size; ULift changes neither points nor their equivalence relation.
- A represented smooth quotient: `∃ X q, Smooth X.hom ∧ ...`, with X an
  S-scheme. The first universal base-change clause provides the representing
  presheaf isomorphism `e` for all T and t, in particular `t = 𝟙 S`.
  `(Over.map t).op ⋙ uliftYoneda.obj X` is the functor of points of X_T:
  a T-map W → X_T is canonically an S-map W → X by `Over.mapPullbackAdj t`.
  Consequently this is representability, not just a pointwise bijection.
- The projection: q is the same map throughout. The equation with `e.hom`
  identifies its Yoneda map with `relativeSubgroupFppfQuotientMap i t`,
  the coset projection followed by `toSheafify`. Thus q is the quotient
  projection and e is normalized by it, not an unconstrained isomorphism.
- Smooth surjective projection: `Smooth q.left ∧ Surjective q.left`.
- Right H-torsor: the second universal base-change clause is `IsPullback`
  of the first projection and `relativeSubgroupRightTranslation i` against
  q and q. By the universal property of pullback this says exactly that
  `(g,h) ↦ (g,g i(h))` identifies G ×_S H with G ×_X G. It is a scheme
  identity (in the slice category), not an identity only on field points.
  Smooth surjectivity supplies the required local covering property.
- Arbitrary base change: both clauses quantify over every `T : Scheme.{u}`
  and `t : T ⟶ S`, including nonaffine, nonreduced and empty T. The quotient
  clause uses the same pulled-back projection q and the canonical sheaf quotient;
  the torsor clause applies `Over.pullback t` to both actual relation maps and q.
  Pullback preserves products in the slice, so its source is canonically
  G_T ×_T H_T. Compatibility is specified by the projection equation: every
  representing identification agrees with the same canonical quotient map.
  Such normalized identifications are unique since the coset projection followed
  by sheafification is an epimorphism. Thus iterated base-change identifications
  also agree; no arbitrary independent isomorphisms are being selected.
- Conditional properness: the final implication assumes a closed immersion j
  of each X_Ω into `ProjectiveSpace (ULift (Fin (n+1))) (Spec (.of Ω))`,
  for some `n : ℕ`, and explicitly requires j to commute with structure maps.
  The displayed quotient identification over that geometric point identifies
  X_Ω with G_Ω/H_Ω. Thus this premise is exactly projective representability
  of the geometric quotient, expressed on its already constructed representative;
  it is not an assumption of properness or of global projectivity of X.
  The conclusion is `IsProper X.hom`.

Dependency declarations used (source declarations and their docstrings read):

- `def-weil-affine-spectrum`, `def-pc-scheme`: `AlgebraicGeometry.Spec`,
  `Spec.map`, `Scheme` and `Scheme.Hom`, Mathlib.AlgebraicGeometry.Scheme.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `def-sbc-locally-finite-presentation`: `LocallyOfFinitePresentation`,
  Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation, reexported by Smooth.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, with `IsMonHom` and the
  group on Hom sets, Mathlib.CategoryTheory.Monoidal.Grp and Cartesian.Grp.
  The recorded general internal-group notion is directly usable over S;
  the field-specific subgroup API in GroupScheme.Defs is unnecessary here.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion.
- `def-weil-connected-scheme`: `ConnectedSpace`,
  Mathlib.Topology.Connected.Basic; its geometric-fibre form is the existing
  `GeometricallyConnected` in Mathlib.AlgebraicGeometry.Geometrically.Connected.
- `def-pc-fppf-site`: `Scheme.fppfPrecoverage`, `Scheme.fppfTopology`,
  Mathlib.AlgebraicGeometry.Sites.Fpqc; slice topology `GrothendieckTopology.over`,
  Mathlib.CategoryTheory.Sites.Over. These are jointly surjective flat lfp covers.
- `def-weil-pbc-sheafification`: `CategoryTheory.presheafToSheaf` and
  `toSheafify`, Mathlib.CategoryTheory.Sites.Sheafification, reexported through
  ConcreteSheafification. The construction uses their actual universal adjoint.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`,
  Mathlib.AlgebraicGeometry.Morphisms.Proper.
- `def-nagata-projective-space-base-change`: `AlgebraicGeometry.ProjectiveSpace`
  and `ProjectiveSpace.over`, WeilConjectures.AlgebraicGeometry.ProjectiveSpace.
  ULift (Fin (n+1)) indexes n+1 homogeneous coordinates in universe u.
- `def-weil-geometric-point`: `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic; geometric points are bound inline
  `(Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S)` as recorded.
  `Scheme.SpecToEquivOfField` in Mathlib.AlgebraicGeometry.ResidueField confirms
  this is the prescribed residue-field formulation; it is not needed in the signature.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, pullback.fst/snd,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback, via the actual
  slice pullback functor and `IsPullback`. The slice cartesian structure and
  group object operations are Mathlib's, not duplicate definitions.

Every proof-dependency module that has a recorded Lean module is imported
privately, except modules already publicly imported for statements. Mathlib
Smooth, UniversallyOpen, Fpqc and the other property imports also supply the
recorded Mathlib proof leaves. Proof dependencies not yet carrying declarations
are retained in the node and named in the natural-language proof; none is
replaced by a new theorem or silently removed. No dependency module repair,
statement correction or new independent notion was needed.

Edge cases checked before writing and on rereading: A = 0 gives the empty
base and all objects over it empty; geometric-point premises are vacuous and
properness holds. H = G gives the base quotient, with no requirement that G
be trivial or projective. H = 1 can satisfy self-normalization only for trivial
G (on every test); a nontrivial G is correctly excluded by hself. Non-normal
H is allowed, so the quotient is a sheaf of sets rather than a quotient group.
The dimension-zero projective space is included (n = 0); an empty geometric
fibre is not mistakenly allowed by connectedness. No characteristic, reducedness,
Noetherian assumption, algebraic closedness of the base ring, or affine-only
restriction on test schemes is added. All universes and variables are explicitly
bound. All data definitions are real constructions; one named theorem has sorry.

Searches (2026-10-24):

- msearch leanfinder: "Smooth representable fppf quotient of an affine smooth
  group scheme by a self normalizing smooth closed subgroup, proper if geometric
  fibres projective" returned eight hits including Smooth, Proj properness,
  and Galois-category abstract quotients; none states this relative theorem.
- msearch loogle: `"Scheme", "quotient"` returned three liftQuotient lemmas
  about ring-ideal quotients of affine spectra; none is a group-scheme quotient.
- msearch grep: `self.normaliz|homogeneous|quotient.*group` in AlgebraicGeometry
  returned 25 hits, predominantly homogeneous polynomial algebra and projective
  spectrum definitions, not the relative self-normalizing quotient theorem.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for self-normaliz, normalizer,
  quotientPresheaf and coset found field-specific homogeneous quotients,
  Borel normalizers, rank-one normalizer interfaces, the group-space action
  quotient, and the relatively ample subtorus theorem. Their signatures were
  read: none states the current arbitrary-ring, noncommutative relative result.
  The free-action theorem is used as a proof import. The additive subgroup
  coset construction is tied to Ga over a field, and the group-space construction
  requires group/action objects in sheaves rather than scheme subgroup data;
  neither is an existing scheme-subgroup coset presheaf usable here without
  constructing additional group/action structures. The present four helpers
  simply specialize the existing coequalizer and sheafification APIs to the
  two canonical scheme maps of this item's quotient.
- Exact-name rg in Mathlib, WeilConjectures and Sheaf for all five delivered
  declarations returned no matches. Searching the upstream sources for the
  node id returned none. No existing exact theorem was found.

Validation: scompile.py compiled the module against the current server sources
in 2.9 seconds, with no errors or non-sorry warnings. The first attempt exposed
missing scoped Hom-group operations; opening `MonObj` repaired that issue.
The wrapper's local disk-space failure was handled by its own successful server
confirmation. No local/global build or shared-repository write was performed.


Resume validation (2026-10-24): retained the saved packet and ran the prescribed
`deliver2.py Q88 lem-sfb-relative-self-normalizing-quotient --no-push` twice.
Both attempts failed in the server compilation wrapper before Lean diagnostics:
`sandbox Sheaf.Stage2.Sandbox0` followed by
`resource exhausted (error code: 28, no space left on device)`.
No push was attempted after these failures. The saved signature was checked
verbatim against lean.statement; only the lean field differs from the current
read-clone node; no line exceeds 100 characters; autoImplicit is false; exactly
one sorry remains, in the named theorem. The packet is unchanged apart from
this validation note and awaits resolution of the server storage failure.


Further resume validation (2026-10-24): the prescribed initial dry run and one
retry both failed after 5.4 seconds with the same server tool diagnostic:
`COMPILE FAILED on the server, nothing pushed: sandbox Sheaf.Stage2.Sandbox0;
resource exhausted (error code: 28, no space left on device)`. No Lean diagnostic
was produced. The current read-clone node still differs from this packet only
in `lean`; the recorded signature remains verbatim in the module, all Lean
lines are within 100 characters, autoImplicit is disabled, and the sole sorry
is the named theorem. No source or node changes were made and no push occurred.
The server storage failure persists; the saved packet is retained.


Final resume validation (2026-10-24): inspected the retained report and module,
then ran the required initial deliver2.py --no-push and one retry. Both failed
with exit code 1 after 5.4 seconds before any Lean diagnostic:
`COMPILE FAILED on the server, nothing pushed: sandbox Sheaf.Stage2.Sandbox0;
resource exhausted (error code: 28, no space left on device)`.
Rechecked against the current read-clone node: only lean differs, the recorded
signature occurs verbatim, autoImplicit is false, every Lean line is at most
100 characters, and the sole sorry is the named theorem. No module or node
changes were made. Nothing was pushed; packet retained for server-tool recovery.


Resume validation (2026-10-24 10:40 UTC): inspected the saved report and retained packet.
Ran the required initial `deliver2.py Q88 lem-sfb-relative-self-normalizing-quotient --no-push` and one retry.
Both exited 1 after 5.4 seconds before Lean diagnostics with
`sandbox Sheaf.Stage2.Sandbox0; resource exhausted (error code: 28, no space left on device)`.
The current read-clone node differs only in `lean`; the recorded signature
is verbatim, autoImplicit is disabled, the longest Lean line is 87
characters, and the sole sorry is the named theorem on line 170.
No module or node edits, direct git operations, or push were performed.
Packet retained; server storage failure still prevents validation.

Resume validation (2026-10-24 10:44 UTC): inspected the retained packet and ran
`deliver2.py Q88 lem-sfb-relative-self-normalizing-quotient --no-push` twice.
Both failed after 5.4 seconds, before Lean diagnostics, with
`COMPILE FAILED on the server, nothing pushed: sandbox Sheaf.Stage2.Sandbox0;
resource exhausted (error code: 28, no space left on device)`.
The packet node still differs from the current read-clone node only in `lean`;
its signature is verbatim, autoImplicit is disabled, the longest Lean line is
87 characters, and the sole sorry is the named theorem. No repair note exists.
No module or node changes or push were performed; the saved packet is retained.

Resume validation (2026-10-24 10:47 UTC): inspected the saved packet and ran the required
initial `deliver2.py Q88 lem-sfb-relative-self-normalizing-quotient --no-push`
and one retry. Both failed after 5.4 seconds before Lean diagnostics with
`COMPILE FAILED on the server, nothing pushed: sandbox Sheaf.Stage2.Sandbox0;
resource exhausted (error code: 28, no space left on device)`.
The current read-clone node differs only in `lean`; the recorded signature is
verbatim, autoImplicit is disabled, the longest Lean line is 87 characters, and
the sole sorry is the named theorem. No repair note exists. No module or node
changes or push were performed. The saved packet is retained.

Resume validation (2026-10-24 10:50 UTC): inspected the saved report and ran the required
initial `deliver2.py Q88 lem-sfb-relative-self-normalizing-quotient --no-push`
and one retry. Both failed after 5.4 seconds before Lean diagnostics with
`COMPILE FAILED on the server, nothing pushed: sandbox Sheaf.Stage2.Sandbox0;
resource exhausted (error code: 28, no space left on device)`.
The saved node differs from the current read-clone node only in `lean`; its
signature is verbatim, autoImplicit is disabled, the longest line is 87
characters, and the only sorry is the named theorem on line 170. No repair
note exists. No module or node changes or push were performed; packet retained.

Resume validation (2026-10-24 10:55 UTC): inspected the saved packet and ran the required
initial `deliver2.py Q88 lem-sfb-relative-self-normalizing-quotient --no-push`
and one retry. Both exited 1 after 5.4 seconds before Lean diagnostics with
`COMPILE FAILED on the server, nothing pushed: sandbox Sheaf.Stage2.Sandbox0;
resource exhausted (error code: 28, no space left on device)`.
The node differs from the current read clone only in `lean`; the signature is
verbatim, autoImplicit is disabled, the longest Lean line is 87 characters,
and the only sorry is the named theorem on line 170. No repair note exists.
No module or node edits or push were performed; the packet is retained.

Resume validation (2026-10-24 10:59 UTC): the initial dry run encountered the prior server storage error;
the retry succeeded. deliver2.py --no-push reported OK at commit 28ca1857d41:
server preflight and both sandbox and library-file compilation passed.
Retained the Lean module and node unchanged. Self-check confirmed that only
lean differs from the current node, the signature is verbatim, autoImplicit
is false, the longest line is 87 characters, and the sole sorry is the named
theorem. No repair note is present. The earlier storage blockage is resolved.

## Second reading by Q88

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
