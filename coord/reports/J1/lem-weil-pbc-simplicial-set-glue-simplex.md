## Worker report

The module `Sheaf.AlgebraicTopology.GlueSimplex` states `SSet.glue_simplex`. It models a simplicial subset as a Mathlib `SSet.Subcomplex` of an ambient simplicial set `X`, with `hUV : U ≤ V`; the simplex `x` is a simplex of `V.toSSet` outside `U` in degree `n`. The hypotheses `hbelow`, `hat`, and `habove` render respectively (1) equality in degrees below `n`, (2) the degree-`n` union with the singleton `x`, and (3) every higher simplex outside `U` is degenerate. The definition `a := SSet.yonedaEquiv.symm x` is the morphism from the standard simplex. The conclusion existentially supplies the boundary restriction `b`; its first conjunct is commutativity after the inclusion `Subcomplex.homOfLE hUV`, and its second conjunct is the pushout universal property `IsPushout b (SSet.boundary n).ι (Subcomplex.homOfLE hUV) a`.

Dependency declarations used: `SSet`, `SSet.Subcomplex`, and `SSet.degenerate` from Mathlib's simplicial-set API (the dependency node `def-weil-pbc-simplicial-set` records these); `SSet.boundary` and `SSet.Subcomplex.ι` from `Mathlib.AlgebraicTopology.SimplicialSet.Boundary`; `SSet.yonedaEquiv` from `Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex`; `IsPushout` from `CategoryTheory.Limits`.

Edge cases checked: `n = 0` is represented directly by the natural-number degree and Mathlib's `SSet.boundary 0` (the empty subcomplex); the theorem has no artificial positive-degree assumption. Empty boundaries and empty `U` are therefore permitted. Higher-degree degeneracy is expressed using `SSet.degenerate` at each natural degree.

Searches: the node's recorded LeanSearch and LeanFinder searches found only general skeleton pushout results; grep of Mathlib confirmed `SSet.boundary`, `SSet.degenerate`, `SSet.yonedaEquiv`, and `SSet.relativeCellComplexOfMono.isPushout`, the latter being too general to state this lemma directly. `rg` over `WeilConjectures/` and `lean/Sheaf` found no existing declaration of this lemma.

## Earlier second reading (a previous round; superseded)

The file and node were read independently. `SSet.Subcomplex` supplies the common ambient simplicial set and inclusion; each hypothesis matches the corresponding degree condition in the node. The Yoneda map gives exactly the simplex map `a`, while the commutative boundary equation and `IsPushout` encode the stated square and its universal property. No mismatch was found.

## Second reading by J1

Read the node's complete statement and all four proof steps, Stacks simplicial.tex
Lemma 018R (lemma-glue-simplex), the section on simplicial sets and Definition 016A,
Lemma 0177 (lemma-simplex-map), and hypercovering.tex Lemma 01GM's use of 018R.
The .tex files were read at /home/ubuntu/c1-stacks-review because literature's
source checkout is absent here. The source assumes arbitrary simplicial sets;
there is no finiteness or nonemptiness assumption on this lemma.

Object/hypothesis/conclusion inventory and H3 verdicts:

1. Simplicial sets and simplicial subset U contained in V: `{X : SSet.{u}}`,
   `(U V : X.Subcomplex)`, `(hUV : U ≤ V)`; exact. Read the sole statement
   dependency def-weil-pbc-simplicial-set and its Mathlib declarations:
   Basic.lean:36 identifies SSet with simplicial objects in Type u;
   Subcomplex.lean:45,52,63,74 identifies a subcomplex with a subfunctor,
   its underlying simplicial set and inclusions. A common ambient X imposes
   no extra hypothesis: any U contained in V is represented with X = V
   and the upper subcomplex equal to top. Subtype carriers change no objects.
2. Nonnegative degree: `{n : ℕ}`; exact, including zero.
3. Standard simplex with simplices the monotone maps into [n]: `Δ[n]`;
   exact. Read StdSimplex.lean:39,68: uliftYoneda and objEquiv implement
   these maps up to the canonical ULift bijection, with precomposition.
4. Boundary consisting of nonsurjective maps: `(SSet.boundary n).toSSet`
   and `(SSet.boundary n).ι`; exact. Read Boundary.lean:36 and boundary_zero.
   The source's (n-1)-skeleton boundary is precisely this subset.
5. Distinguished simplex in V_n outside U_n: the subtype binder `x` and
   `hx : x.1 ∉ U.obj (op (mk n))`; exact, membership in V is in x's type.
6. Equality V_i = U_i below n: `hbelow`; exact, all natural i < n.
7. Equality V_n = U_n union {x}: `hat`; exact equality of ambient subsets.
8. Every higher simplex outside U is degenerate: `habove`; exact. Read
   Degenerate.lean:36: a lower-dimensional operator image is the node's
   definition, not a weaker degeneracy in the unrelated ambient X.
9. Map a sends a monotone map phi to V(phi)(x): `SSet.yonedaEquiv.symm x`;
   exact. Read StdSimplex.lean:157 and its naturality/identity lemmas.
10. Boundary image lies in U and b is the restriction: existential `b` and
    `b ≫ Subcomplex.homOfLE hUV = boundary.ι ≫ yonedaEquiv.symm x`;
    exact. Evaluating the equality gives boundary containment. The inclusion
    is injective, so b is necessarily the unique restriction, not an arbitrary map.
11. Commutative square is a pushout, with a unique extension for every
    compatible g and h: `IsPushout b boundary.ι (Subcomplex.homOfLE hUV)
    (SSet.yonedaEquiv.symm x)`; exact. Read IsPullback/Defs.lean:78:
    IsPushout extends CommSq and gives IsColimit of that PushoutCocone,
    which is exactly the existence and uniqueness quantified in the node.
    The separate equality is redundant but matches the explicit restriction clause.
12. Zero-degree coproduct: covered by the same IsPushout and boundary_zero;
    compatibility over the empty boundary is vacuous, giving U coproduct Delta[0].

Edge cases: n = 0 is allowed; hbelow then has no instances, and boundary 0 is
bottom. U may be empty. Empty V (or empty ambient X) cannot supply x, exactly
as in the source. There is no index set, zero module, scheme, ring, or
characteristic to constrain. Universe u is explicitly declared and arbitrary;
no small fixed universe, extra typeclass, or finiteness assumption occurs.
IsPushout quantifies over arbitrary targets in SSet.{u}; the argument works in
every u. All binders are bound explicitly.

Independent searches used msearch.py with different wording from the worker:
LeanFinder query "A simplicial set with exactly one new nondegenerate simplex is
obtained by cobase change of the boundary inclusion" returned Quillen I/J,
boundary membership, and horn-specific pushouts, none this statement.
LeanSearch query "A subfunctor inclusion of simplicial sets whose complement
consists of degeneracies of a single simplex forms a pushout with the standard
simplex and its boundary" was unavailable (HTTP internal server error); no
verdict is inferred from that failure. Loogle query `SSet.boundary` returned the
boundary definition and its API, not this attachment theorem. msearch grep
`glue.?simplex|isPushout|attaching` in AlgebraicTopology/SimplicialSet and direct
rg searches for glue_simplex, glueSimplex, simplicial pushouts/attachments and
nondegenerate simplices across Mathlib, the entire WeilConjectures tree,
lean/Sheaf and dag/lean_names_upstream.json found no exact existing declaration.
Opened Skeleton.lean's relativeCellComplexOfMono maps and isPushout: it attaches
an indexed coproduct to successive relative skeleta, and identifying those
skeleta and its singleton index requires the argument of this node. It is not
an existing statement of this node. No private notion, new definition node,
or dependency module is needed: the dependency's recorded Mathlib API is usable.

Mismatches repaired: the statement used a let-bound simplex map, prohibited
by the project convention because stage 3 cannot unfold the resulting have;
inlined yonedaEquiv.symm x in both occurrences without changing meaning.
The theorem docstring only referred to four proof steps; replaced this with
the complete four-step proof including the named face-factorization and
nondegenerate-decomposition dependencies, naturality's two cases, uniqueness,
and the n = 0 coproduct. Added the standard copyright/license header, fixed
binder indentation, and replaced the unused Skeleton import with the direct
IsPushout definitions import. No mathematical hypothesis or conclusion changed;
no node statement correction was necessary. The node's lean.statement was
synchronized verbatim to the new signature. The only proof is `by sorry`;
no data definition or hollow proof-bearing definition was introduced.

Validation: scompile.py compiled the complete delivery (one module) on the
server in 1.1 seconds, exit code 0, with no warnings. Checked the signature
and universe binders by eye and all lines satisfy the 100-character convention.
