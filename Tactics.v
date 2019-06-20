(** [tuple_inversion] inverses an equality of tuple into equalities for
    each component. *)
Ltac tuple_inversion :=
  match goal with
    | [ H : (_, _, _, _) = (_, _, _, _) |- _ ] => invc H
    | [ H : (_, _, _) = (_, _, _) |- _ ] => invc H
    | [ H : (_, _) = (_, _) |- _ ] => invc H
  end.
