# The theorem of the cube over a general base

Let $S$ be any scheme and let $\pi:A\to S$ be an abelian scheme, with identity section $e:S\to A$. Let $L$ be a line bundle on $A$, and write $L^{-1}=L^\vee$. No reducedness or Noetherian hypothesis on $S$ is required.

Set

$$
A^3=A\times_S A\times_S A,
\qquad p_i:A^3\to A\quad(i=1,2,3),
\qquad \pi_3=\pi\circ p_i:A^3\to S.
$$

Here $p_i$ is the $i$th projection. Define the sum maps

$$
\begin{aligned}
m_{ij}:A^3&\longrightarrow A,
& (x_1,x_2,x_3)&\longmapsto x_i+x_j\quad(1\le i<j\le3),\\
m_{123}:A^3&\longrightarrow A,
& (x_1,x_2,x_3)&\longmapsto x_1+x_2+x_3.
\end{aligned}
$$

The zero map is $e\circ\pi_3$, whose pullback of $L$ is $\pi_3^*(e^*L)$.

**Canonical statement.** Define the seven-term line bundle

$$
\begin{aligned}
C_7(L)={}&m_{123}^*L
\otimes m_{12}^*(L^{-1})
\otimes m_{13}^*(L^{-1})
\otimes m_{23}^*(L^{-1})\\
&\otimes p_1^*L\otimes p_2^*L\otimes p_3^*L.
\end{aligned}
$$

The relative theorem of the cube gives a canonical isomorphism

$$
\boxed{c_L:C_7(L)\xrightarrow{\sim}\pi_3^*(e^*L).}
$$

Equivalently, the eight-term line bundle

$$
\begin{aligned}
\Theta(L)={}&m_{123}^*L
\otimes m_{12}^*(L^{-1})
\otimes m_{13}^*(L^{-1})
\otimes m_{23}^*(L^{-1})\\
&\otimes p_1^*L\otimes p_2^*L\otimes p_3^*L
\otimes\pi_3^*((e^*L)^{-1})
\end{aligned}
$$

has a canonical trivialization

$$
\boxed{\tau_L:\Theta(L)\xrightarrow{\sim}\mathcal O_{A^3}.}
$$

These isomorphisms are natural under isomorphisms of line bundles and compatible with arbitrary base change. They require no chosen trivialization of $e^*L$. One obtains this formulation from the usual rigidified cube theorem by applying it to $L\otimes\pi^*((e^*L)^{-1})$, which is canonically rigidified by evaluation. See [Lan, Proposition 3.2.3.1](https://www.kwlan.org/articles/cpt-PEL-type-thesis-revision-dense.pdf#page=82).

**Canonical normalization.** On each coordinate face $x_i=0$ (the image of $e$ in that coordinate), the factors of $\Theta(L)$ cancel canonically. For example, on $x_3=0$,

$$
m_{123}=m_{12},\qquad m_{13}=p_1,\qquad
m_{23}=p_2,\qquad p_3=e\circ\pi_3.
$$

The trivialization $\tau_L$ is the unique one restricting to these cancellation trivializations. Indeed, two such trivializations differ by a global unit on $A^3$; since $(\pi_3)_*\mathcal O_{A^3}=\mathcal O_S$, this unit comes from $S$, and face normalization forces it to be $1$. Thus “canonical” specifies an actual isomorphism, not merely an equality in the Picard group. See also [Conrad, Theorem 3.1.6 and its proof](https://math.stanford.edu/~conrad/249CS15Page/handouts/abvarnotes.pdf#page=26).

**Why the seven-term trivialization needs a choice.** A rigidification $\epsilon:e^*L\xrightarrow{\sim}\mathcal O_S$ gives

$$
C_7(L)\xrightarrow{c_L}\pi_3^*(e^*L)
\xrightarrow{\pi_3^*\epsilon}\mathcal O_{A^3}.
$$

Such a rigidification exists only when $e^*L$ is trivial. Replacing $\epsilon$ by $u\epsilon$, for $u\in\Gamma(S,\mathcal O_S^\times)$, multiplies this seven-term trivialization by $\pi_3^*u$. The eight-term trivialization $\tau_L$ involves no such choice. The identity section $e$ itself is already part of the abelian scheme structure.
