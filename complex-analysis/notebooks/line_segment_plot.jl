using Plots

"""
Plot a line segment with arrows at the middle point.

# Arguments
- `z0::Complex`: The start point of the line segment.
- `z1::Complex`: The end point of the line segment.
- `arrow_distance::Real=0.5`: The distance from the arrow to the line segment.
- `arrow_length::Real=0.5`: The length of the arrow.
- `color::Symbol=:black`: The color of the line segment.
- `linewidth::Real=1.0`: The width of the line segment.
- `linestyle::Symbol=:solid`: The style of the line segment.
- `which_arrow::Symbol=:both`: Which arrow to plot. It can be `:left`, `:right`, or `:both`.
"""
function plot_line_segment!(
    z0::Complex,
    z1::Complex;
    arrow_distance::Real=0.5,
    arrow_length::Real=0.5,
    color::Symbol=:black,
    linewidth::Real=1.0,
    linestyle::Symbol=:solid,
    which_arrow::Symbol=:both,
)::Plots.Plot
    # The middle point of the line
    z_mid = (z0 + z1) / 2

    # The direction and normal vectors
    direction_vec = (z1 - z0) / abs(z1 - z0)
    normal_vec = (z1 - z0) * 1im / abs(z1 - z0)

    # Middle points of the arrows
    left_arrow_mid = z_mid + arrow_distance * normal_vec
    right_arrow_mid = z_mid - arrow_distance * normal_vec

    # Start points of the arrows
    left_arrow_start = left_arrow_mid - 0.5 * arrow_length * direction_vec
    left_arrow_end = left_arrow_mid + 0.5 * arrow_length * direction_vec

    # End points of the arrows
    right_arrow_start = right_arrow_mid - 0.5 * arrow_length * direction_vec
    right_arrow_end = right_arrow_mid + 0.5 * arrow_length * direction_vec

    # Plot the line segment
    plot!(
        [real(z0), real(z1)],
        [imag(z0), imag(z1)],
        color=color,
        linewidth=linewidth,
        linestyle=linestyle,
    )

    # Plot the left arrow
    if which_arrow == :left || which_arrow == :both
        quiver!(
            [real(left_arrow_start)],
            [imag(left_arrow_start)],
            quiver=([real(left_arrow_end - left_arrow_start)], [imag(left_arrow_end - left_arrow_start)]),
            color=color,
        )
    end

    # Plot the right arrow
    if which_arrow == :right || which_arrow == :both
        quiver!(
            [real(right_arrow_start)],
            [imag(right_arrow_start)],
            quiver=([real(right_arrow_end - right_arrow_start)], [imag(right_arrow_end - right_arrow_start)]),
            color=color,
        )
    end

    plot!()
end